-- Prove2me | Theorems.Thm_GapAgnosticGS_Supplement_theorem_5_4
-- name    : GapAgnosticGS.Supplement.theorem_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:34:54.386228+00:00
-- url     : https://prove2.me/theorems/0f0ab04d-d080-4f91-aa87-785ac0e6587e
-- title:
--   Theorem 5.4 — basis-oblivious zero-phase amplification for a Hermitian-unitary block encoding
-- statement:
--   Let $U$ be a Hermitian unitary on $B\otimes S$, where $B$ is a finite auxiliary register with a basis state $|0\rangle_B$ and $S=\mathbb C^n$ has its computational basis, and let $D_U=(\langle0|_B\otimes I_S)U(|0\rangle_B\otimes I_S)$ have eigenvalues
--   $$
--   1=\lambda_1=\cdots=\lambda_r>\lambda_{r+1}\ge\cdots\ge\lambda_n\ge0,\qquad 1\le r<n .
--   $$
--   Let $G_U$ be the eigenspace of $D_U$ at eigenvalue $1$ and $\theta_j=\arccos\lambda_j$ for $j>r$. The learner has controlled access to $U$ and knows $r$ and a lower bound $0<\underline\theta\le\theta_{r+1}$.
--
--   There are absolute constants $C>0$ and $K$ such that for every $n$, every such register $B$, every $r$ with $1\le r<n$, every $\underline\theta>0$ and every $\delta,\epsilon\in(0,1/3)$ there is one algorithm which, for every such $U$, outputs with probability at least $1-\delta$ a state $\rho$ on $S$ within trace distance $\epsilon$ of some density matrix $\sigma$ supported on $G_U$, using in expectation at most
--
--   $$
--   C\Big[\frac1{\underline\theta^2}+\frac1r\sum_{j=r+1}^n\frac1{\theta_j^2}\Big]^{1/2}\Big(\log\frac{n}{\delta\epsilon\underline\theta}\Big)^K
--   $$
--
--   controlled queries to $U$.
--
--   The algorithm never learns an eigenbasis of $D_U$: it tests the phases of the walk $(2\Pi_0-I)U$ at successively finer resolutions. Theorem 5.1 is the case of the discriminant block encoding $O_P^\dagger S_{1\leftrightarrow2}O_P$ with $r=1$.
--
--   **Formalization Note** $D_U$ is the published `DepthOptQC.Synth.block b₀ U` $=V_0^\dagger UV_0$ with $V_0=|0\rangle_B\otimes I_S$; the eigenvalues are `descEigenvalues (DepthOptQC.Synth.block b₀ U)`, 0-based. "$\sigma$ supported on $G_U$" is $D_U\sigma=\sigma$ for a density matrix $\sigma$; trace distance is $\tfrac12\|\rho-\sigma\|_1$.
--
--   Differences from the source:
--   - encoding: B an auxiliary register with |0⟩_B, S with known basis {|x⟩} → B any finite type with a distinguished element b₀, S = Fin n, both quantified before the algorithm; reason: the algorithm may depend on the registers, not on U
--   - encoding: D_U has eigenvalues 1 = λ_1 = ⋯ = λ_r > λ_{r+1} ≥ ⋯ ≥ λ_n ≥ 0 → with λ = descEigenvalues D_U (0-based): λ_j = 1 for j < r, λ_j < 1 for j ≥ r, λ_j ≥ 0 for all j; reason: the decreasing order is built into descEigenvalues
--   - encoding: a lower bound 0 < θ̲ ≤ θ_{r+1} → 0 < θ̲ and θ̲ ≤ θ_j for every j > r; reason: θ_{r+1} is the smallest θ_j, j > r
--   - encoding: a state on S within trace distance ϵ of a state supported on G_U → ∃ density matrix σ with D_U σ = σ and traceDist(ρ, σ) ≤ ϵ; reason: the range of σ lies in ker(D_U − 1) exactly when D_U σ = σ
--   - encoding: controlled queries to U → controlled U and U† queries of the OracleAlg; reason: U is Hermitian, so U† = U
--   - encoding: O(·), Ω(·), polylog, Õ → absolute constants C > 0, K ∈ ℕ (and c > 0) chosen before every parameter, polylog(x) = (log x)^K; reason: base mission convention; the bounds are uniform in the instance
--   - encoding: a quantum algorithm with controlled access to the oracle → one OracleAlg of the base mission, fixed before the instance; controlled uses of the oracle and its inverse each count one query; reason: an algorithm chosen after the instance would know the answer; base algorithm model
-- source:
--   Heidari–Moharrami–Tavakoli–Zhang, Gap-Agnostic Ground-State Preparation via Quantum Bandits, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Theorem 5.4, pp.24–25 (PDF pp.25–26), Eq. (21)

import Definitions.Def_GapAgnosticGS_OracleAlg_successProb
import Definitions.Def_GapAgnosticGS_OracleAlg_expQueries
import Definitions.Def_GapAgnosticGS_Supplement_descEigenvalues
import Definitions.Def_DepthOptQC_Synth_amp
import Definitions.Def_ClonableQMASep_Main_Channels
open QAlgorithms ClonableQMASep.Main

namespace GapAgnosticGS.Supplement

open scoped ENNReal

/-- Heidari–Moharrami–Tavakoli–Zhang, *Gap-Agnostic Ground-State Preparation via Quantum Bandits*, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Theorem 5.4 (Basis-oblivious zero-phase amplification), pp.24–25 (PDF pp.25–26): "Let U be
a Hermitian unitary on B ⊗ S, where B is an auxiliary register and S is a system register with
known computational basis {|x⟩_S}_{x=1}^n. Let D_U be the block of U corresponding to B = 0:
D_U := (⟨0|_B ⊗ I_S) U (|0⟩_B ⊗ I_S). Suppose D_U has eigenvalues
1 = λ_1 = ⋯ = λ_r > λ_{r+1} ≥ ⋯ ≥ λ_n ≥ 0, 1 ≤ r < n. Let G_U be the eigenspace of D_U at
eigenvalue 1, and define θ_j := arccos(λ_j) for j > r. Suppose we have controlled access to U and
know both the multiplicity r and a lower bound 0 < θ̲ ≤ θ_{r+1}. For any δ, ϵ ∈ (0, 1/3), there is
an algorithm that, with probability at least 1 − δ, prepares a state on S within trace distance ϵ
of a state supported on G_U. The expected number of controlled queries to U is
O([1/θ̲² + (1/r) Σ_{j=r+1}^n 1/θ_j²]^{1/2} polylog(n/(δϵθ̲))). (21)"

There are absolute `C > 0`, `K` such that for every `n`, every finite auxiliary register `B` with
a basis state `b₀` (the paper's `|0⟩_B`), every `r` with `1 ≤ r < n`, every `θ̲ > 0` and
`δ, ϵ ∈ (0, 1/3)` one algorithm, fixed before `U`, satisfies for every Hermitian unitary `U` on
`B ⊗ ℂⁿ` whose block `D_U` has decreasing eigenvalues `λ_1 = ⋯ = λ_r = 1 > λ_{r+1} ≥ ⋯ ≥ λ_n ≥ 0`
and `θ̲ ≤ θ_j` for all `j > r`: with probability at least `1 − δ` it halts with a state `ρ` on `S`
for which there is a density matrix `σ` supported on `G_U = ker(D_U − 1)` with
`D(ρ, σ) ≤ ϵ`, and its expected number of controlled queries to `U` is at most
`C √(1/θ̲² + (1/r) Σ_{j > r} 1/θ_j²) · log^K(n/(δϵθ̲))`.

**Formalization Note.** `λ_j` is `descEigenvalues D_U (j − 1)` (0-based, so "j ≤ r" is `j < r` and
"j > r" is `r ≤ j`); the sorted order is built in, so the hypothesis is `λ = 1` below `r`, `λ < 1`
from `r` on, and `λ ≥ 0` everywhere. "θ̲ ≤ θ_{r+1}" is `θ̲ ≤ θ_j` for all `j > r` (`θ_{r+1}` is the
smallest). "σ supported on G_U" is `D_U σ = σ` (the range of `σ` lies in the 1-eigenspace).
`D_U` is the published `DepthOptQC.Synth.block b₀ U = V₀† U V₀` with `V₀ = |b₀⟩_B ⊗ I_S`, the
paper's `(⟨0|_B ⊗ I_S) U (|0⟩_B ⊗ I_S)` (auxiliary register first). The algorithm may depend on `B`, `b₀`, `n`, `r` and `θ̲`, not on `U`. Queries are the `OracleAlg`
controlled `U`/`U†` queries (`U† = U`). The trace distance is `½‖ρ − σ‖₁` (`traceDist`). -/
theorem theorem_5_4 :
    ∃ (C : ℝ) (K : ℕ), 0 < C ∧
      ∀ (n : ℕ) (B : Type) [Fintype B] [DecidableEq B] (b₀ : B) (r : ℕ), 1 ≤ r → r < n →
      ∀ (θl δ ϵ : ℝ), 0 < θl → δ ∈ Set.Ioo 0 (1 / 3) → ϵ ∈ Set.Ioo 0 (1 / 3) →
      ∃ alg : OracleAlg (B × Fin n) (Fin n) Unit,
        ∀ U ∈ Matrix.unitaryGroup (B × Fin n) ℂ, U.IsHermitian →
          (∀ j : Fin n, ((j : ℕ) < r → descEigenvalues (DepthOptQC.Synth.block b₀ U) j = 1) ∧
            (r ≤ (j : ℕ) → descEigenvalues (DepthOptQC.Synth.block b₀ U) j < 1) ∧
            0 ≤ descEigenvalues (DepthOptQC.Synth.block b₀ U) j) →
          (∀ j : Fin n, r ≤ (j : ℕ) →
            θl ≤ Real.arccos (descEigenvalues (DepthOptQC.Synth.block b₀ U) j)) →
          ENNReal.ofReal (1 - δ) ≤ alg.successProb U
              (fun _ ρ => ∃ σ : Matrix (Fin n) (Fin n) ℂ, IsDensity σ ∧
                DepthOptQC.Synth.block b₀ U * σ = σ ∧ traceDist ρ σ ≤ ϵ) ∧
          alg.expQueries U ≤ ENNReal.ofReal (C * Real.sqrt (1 / θl ^ 2 + (1 / (r : ℝ)) *
              ∑ j ∈ Finset.univ.filter (fun j : Fin n => r ≤ (j : ℕ)),
                1 / Real.arccos (descEigenvalues (DepthOptQC.Synth.block b₀ U) j) ^ 2) *
            Real.log (n / (δ * ϵ * θl)) ^ K) := by sorry

end GapAgnosticGS.Supplement
