-- Prove2me | Theorems.Thm_OptQJunta_theorem_3_19
-- name    : OptQJunta.theorem_3_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:21:22.464625+00:00
-- url     : https://prove2.me/theorems/e74193bc-feb4-4862-839b-a59e00f32fde
-- title:
--   Theorem 3.19 — Union Size Testing from a reversible sampler with $O(\sqrt{k/\delta})$ queries
-- statement:
--   Fix integers $1\le k<n$ and $0<\delta\le1$. Given ordinary queries to a reversible sampler $A$ for a distribution $\mathcal D$ on $2^{[n]}$ and to its inverse $A^\dagger$, there is a quantum algorithm for Problem 3.1 on the ground set $[n]$ that succeeds with probability at least $9/10$ and uses $O(\sqrt{k/\delta})$ queries. The guarantee holds for all auxiliary outputs and unitary extensions of the sampler.
--
--   Precisely: there is an absolute $C>0$ such that for all such $k,n,\delta$ and every finite auxiliary space with zero state $a_0$, some query algorithm with at most $C\sqrt{k/\delta}$ calls to $A$ or $A^\dagger$ satisfies, for **every** unitary $A$ on the sampler's space with induced distribution $\mathcal D$:
--
--   $$
--   \text{YES}(\mathcal D)\Rightarrow\Pr[\text{YES}]\ge\tfrac{9}{10},\qquad \text{NO}(\mathcal D)\Rightarrow\Pr[\text{NO}]\ge\tfrac{9}{10}.
--   $$
--
--   Applied to the Fourier sampler of Lemma 2.34 this is the tester of Theorem 4.2 in its main regime.
--
--   Differences from the source:
--   - reading: $O(\cdot)$ in the query bound → an explicit absolute constant chosen before every parameter of the statement; reason: the standard meaning of the asymptotic notation; §4 calls its constants absolute (Lemma 4.5, p.56)
--   - encoding: a reversible sampler: a unitary $A$ on a finite-dimensional space with an $n$-qubit subset register, $|0\rangle$ the all-zero state of all registers (§2.5.5, p.24) → a unitary matrix on $\mathbb C^{\mathrm{Finset}(\mathrm{Fin}\,n)\times\mathrm{Aux}}$ for an arbitrary finite $\mathrm{Aux}$, with $|0\rangle$ the basis state $(\varnothing,a_0)$; the algorithm calls $A$ or $A^\dagger$ in a fixed pattern; reason: a subset is its incidence string and the auxiliary registers are $\mathrm{Aux}$; an adaptive choice between $A$ and $A^\dagger$ is simulated by the alternating pattern at twice the cost, so the query bound changes by a constant factor only
--   - encoding: a procedure that prepares states and measures $\Pi$ (or a circuit with an answer bit) → a `SamplerAlg`/`SamplerCirc` in unitary form whose output is read from the final computational-basis measurement; reason: deferred measurement; "some measurement succeeds" is the output `true`
--   - encoding: ground set $[n]=\{1,\dots,n\}$ → `Fin n` (coordinates from $0$), subsets as `Finset (Fin n)`; reason: a relabelling; same instances
-- source:
--   Bao, Gao, Yao, Optimal Quantum Junta Testing, preprint (version of November 3, 2026, sha256 a97d09a4…), Theorem 3.19, p.38

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_OptQJunta_SamplerAlg

open QAlgorithms

namespace OptQJunta

/-- **Theorem 3.19** (Upper bound for Union Size Testing from a reversible sampler; Bao, Gao, Yao, *Optimal Quantum Junta Testing*, preprint, version of November 3, 2026, sha256 a97d09a4…, p.38). Fix
integers `1 ≤ k < n` and `0 < δ ≤ 1`. Given ordinary queries to a reversible sampler `A` for a
distribution `𝒟` on `2^{[n]}` and to its inverse `A†`, there is a quantum algorithm for Problem 3.1 on
the ground set `[n]` that succeeds with probability at least `9/10` and uses `O(√(k/δ))` queries.
The guarantee holds for all auxiliary outputs and unitary extensions of the sampler.

**Formalization Note** The constant `C` is absolute (before `k`, `n`, `δ`). The sampler acts on
`ℂ^{Finset (Fin n) × Aux}` for an arbitrary finite auxiliary space `Aux` with zero state `(∅, a₀)`;
the algorithm (with its own finite workspace `W`, its call pattern of `A`/`A†`, and its unitaries)
may depend on `Aux` and `a₀`, and must succeed for **every** unitary `A`, whose distribution is
`samplerDist a₀ A` (§2.5.5: "for every unitary `A` with this action on `|0⟩`"). Output `true` = YES. -/
theorem theorem_3_19 :
    ∃ C : ℝ, 0 < C ∧ ∀ k n : ℕ, 1 ≤ k → k < n → ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ (Aux : Type) [Fintype Aux] [DecidableEq Aux] (a₀ : Aux),
        ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (T : ℕ)
          (M : SamplerAlg (Finset (Fin n) × Aux) W T) (out : (Finset (Fin n) × Aux) × W → Bool),
          (T : ℝ) ≤ C * Real.sqrt (k / δ) ∧
          ∀ A : Matrix.unitaryGroup (Finset (Fin n) × Aux) ℂ,
            (UnionYes (samplerDist a₀ (A : Matrix (Finset (Fin n) × Aux) (Finset (Fin n) × Aux) ℂ)) k →
                9 / 10 ≤ M.outputProb (A : Matrix (Finset (Fin n) × Aux) (Finset (Fin n) × Aux) ℂ) out true) ∧
              (UnionNo (samplerDist a₀ (A : Matrix (Finset (Fin n) × Aux) (Finset (Fin n) × Aux) ℂ)) k δ →
                9 / 10 ≤ M.outputProb (A : Matrix (Finset (Fin n) × Aux) (Finset (Fin n) × Aux) ℂ) out false) := by sorry

end OptQJunta
