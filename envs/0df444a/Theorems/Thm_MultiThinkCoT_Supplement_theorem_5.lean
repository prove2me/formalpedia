-- Prove2me | Theorems.Thm_MultiThinkCoT_Supplement_theorem_5
-- name    : MultiThinkCoT.Supplement.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:59:25.464834+00:00
-- url     : https://prove2.me/theorems/35b345d4-7dc6-4f2e-a499-33d80d0a2d8e
-- title:
--   Theorem 5 — efficient pass@$\kappa$ learner with known provenance in time $\mathrm{poly}(d,T,\kappa,\varepsilon^{-1},\log\delta^{-1})$
-- statement:
--   Let $(\mathcal F_d)_{d\ge1}$ be a hierarchy of base classes over domains $\mathcal X_d\subseteq\{0,1\}^{\le d}$ that admits an efficient Consistent oracle (Definition 1.1) and satisfies $\mathrm{VCdim}(\mathcal F_d)\le\mathrm{poly}(d,T)$ over the prefix domain $\mathcal X_d\times\{0,1\}^{\le T-1}$. Consider instance-dependent CoT supervision with **known provenance** (Definition 6.1): generators $f_1,\dots,f_\kappa\in\mathcal F_d$ realizing a common $h_\star$ end to end, an input distribution $\mathcal D$ and an arbitrary source kernel $\mathcal P(\cdot\mid x)$, and the learner observes $(x^{(i)},j^{(i)},z^{(i)})$ with $z^{(i)}=f_{j^{(i)}}^{\mathrm{CoT}\text{-}T}(x^{(i)})$.
--
--   The learner that applies the Consistent oracle separately to the prefix–next-token pairs of each generator's traces, obtaining $\hat f_1,\dots,\hat f_\kappa$, and returns $\widehat{\mathcal Z}(x)=\{\hat f_j^{\mathrm{CoT}\text{-}T}(x):j\in[\kappa]\}$, run on a polynomially large sample, has the following guarantee. For all $\varepsilon,\delta\in(0,1)$, with probability at least $1-\delta$ over the training sample,
--
--   $$
--   \max_{x\in\mathcal X_d}|\widehat{\mathcal Z}(x)|\le\kappa\qquad\text{and}\qquad\Pr_{x\sim\mathcal D,\ j\sim\mathcal P(\cdot\mid x)}\Big[f_j^{\mathrm{CoT}\text{-}T}(x)\notin\widehat{\mathcal Z}(x)\Big]\le\varepsilon,
--   $$
--
--   and the learner, including the evaluation of $\widehat{\mathcal Z}(x)$ on any $x\in\mathcal X_d$, runs in time $\mathrm{poly}(d,T,\kappa,\varepsilon^{-1},\log\delta^{-1})$.
--
--   Precisely: for every polynomial bound $V(d+T+1)^w$ on the VC dimension there is a sample-size rule $m_5(d,T,\kappa,\varepsilon,\delta)$, and for all polynomial bounds $A(d+n+N+1)^a$ on the oracle's cost on $N$ pairs of maximal length $n$ and $B(d+\ell+1)^b$ on one next-token evaluation on a string of length $\ell$, there are $C,k$ such that the sample size, the cost of every run and the cost of evaluating $\widehat{\mathcal Z}(x)$ at every $x\in\mathcal X_d$ are at most $C\,(d+T+\kappa+\lceil1/\varepsilon\rceil+\lceil\log(1/\delta)\rceil+2)^k$, and the pass@$\kappa$ bound holds with probability at least $1-\delta$.
--
--   Known provenance thus makes the pass@$\kappa$ version of $\kappa$-ConsistentCoT computationally efficient, in contrast with the hardness results for unknown provenance.
--
--   **Formalization Note** The learner and its cost are the definition `MultiThinkCoT.Supplement.alg5` (unit-cost conventions of the published Algorithm 1). Realizability of $h_\star$ is required at every point of $\mathcal X_d$, as in the published mission.
--
--   Differences from the source:
--   - reading: "there is a learning algorithm … that runs in time poly$(d,T,\kappa,\varepsilon^{-1},\log\delta^{-1})$" → the explicit learner of the proof (p.22) with its sample-size rule $m_5$ (depending only on the VC polynomial) and line-by-line cost, with "poly" quantified as for all polynomial cost bounds there are $C,k$; reason: an unrestricted "there is an algorithm" would make the time bound vacuous, and the proof names this learner.
--   - generalization: with probability $\ge1-\delta$, $\max_x|\widehat{\mathcal Z}(x)|\le\kappa$ → $|\widehat{\mathcal Z}(x)|\le\kappa$ and the cost bounds hold for every sample; reason: the learner is deterministic and these bounds hold on every run, which implies the probabilistic statement.
--   - encoding: $\mathcal D\in\Delta(\mathcal X_d)$ and $j^{(i)}\sim\mathcal P(\cdot\mid x^{(i)})$ → $\mathcal D$ a PMF and $(x^{(i)},j^{(i)})$ i.i.d. from the joint law; reason: the two-stage sampling of Definition 6.1 is exactly this joint law.
-- source:
--   Joshi, Magen, Srebro, Tsilivis, Vardi, Learning to Think from Multiple Thinkers: How Chain-of-Thought Heterogeneity Affects Efficient Learnability, arXiv:2604.24737 (held version, sha256 e663a640…), §7.1, Theorem 5 and its proof, pp.21–22 (PDF pp.21–22)

import Mathlib
import Definitions.Def_UnderstandingML_VC
import Definitions.Def_MultiThinkCoT_prefixClass
import Definitions.Def_MultiThinkCoT_endToEndError
import Definitions.Def_MultiThinkCoT_IsConsistentOracle
import Definitions.Def_MultiThinkCoT_Supplement_passErr
import Definitions.Def_MultiThinkCoT_Supplement_alg5

namespace MultiThinkCoT.Supplement

/-- **Theorem 5 (Efficient learner for pass@κ)**, §7.1, pp.21–22 (PDF pp.21–22).
N. Joshi, R. Magen, N. Srebro, N. Tsilivis, G. Vardi, *Learning to Think from Multiple Thinkers:
How Chain-of-Thought Heterogeneity Affects Efficient Learnability*, arXiv:2604.24737 (held
version, sha256 e663a640…).

There is a learning algorithm that, for any hierarchy of base classes `(F_d)_{d≥1}` admitting an
efficient Consistent oracle and satisfying `VCdim(F_d) ≤ poly(d, T)` over `X_d × {0,1}^{≤T−1}`,
under instance-dependent CoT supervision with known provenance, for any `ε, δ ∈ (0, 1)`, with
probability at least `1 − δ` over the training sample returns `Ẑ : X_d → 2^{{0,1}^T}` with
`max_{x∈X_d} |Ẑ(x)| ≤ κ` and `Pr_{x∼D, j∼P(·|x)}[f_j^{CoT-T}(x) ∉ Ẑ(x)] ≤ ε`, in time
`poly(d, T, κ, ε⁻¹, log δ⁻¹)`.

**Formalization Note.**
* The algorithm is the learner of the proof (p.22), `alg5Fit`: it splits the sample by `j(i)`,
  calls the oracle `O` on the prefix–next-token pairs of each group, and returns
  `Ẑ = candSet T (alg5Fit O data)`. Its cost is accumulated by `alg5Cost` and the cost of
  evaluating `Ẑ(x)` by `candSetCost` (see `MultiThinkCoT.Supplement.alg5`). The sample size it
  requests is `m5 d T κ ε δ`, a function that may depend on the VC polynomial `(V, w)` only.
* "poly" is quantified as in the published Theorem 7 (ii): for every polynomial bound
  `V (d + T + 1)^w` on `VCdim(F_d)` over the prefix domain there is a sample-size rule `m5`; for
  all polynomial bounds `oc_d(n, N) ≤ A (d + n + N + 1)^a` on the oracle's cost on `N` pairs of
  maximal length `n` and `ec_d(ℓ) ≤ B (d + ℓ + 1)^b` on one next-token evaluation on a string of
  length `ℓ`, there are `C, k` bounding the sample size, the cost of every run and the cost of
  evaluating `Ẑ(x)` on every `x ∈ X_d` by `C (d + T + κ + ⌈1/ε⌉ + ⌈log(1/δ)⌉ + 2)^k`.
* Definition 6.1: generators `f_1, …, f_κ ∈ F_d` that realize a common `h⋆` on all of `X_d`
  (the published convention), an arbitrary kernel `P : X_d → PMF (Fin κ)`, `(x(i), j(i))` i.i.d.
  from `jointLaw D P`, and known provenance (the learner sees `(x(i), j(i), z(i))`).
* `X_d ⊆ {0,1}^{≤d}`; `d ≥ 1` and `κ ≥ 1` as in the paper. The bound `|Ẑ(x)| ≤ κ` and the cost
  bounds hold for every sample, not only with high probability; the learner is deterministic.
-/
theorem theorem_5 :
    ∀ V w : ℕ, ∃ m5 : ℕ → ℕ → ℕ → ℝ → ℝ → ℕ, ∀ A a B b : ℕ, ∃ C k : ℕ,
      ∀ (Fh : ℕ → Set Gen) (Xh : ℕ → Set (List Bool)),
        (∀ d, ∀ x ∈ Xh d, x.length ≤ d) →
        (∀ d T, ∃ p : ℕ, UnderstandingML.vcDim (prefixClass (Fh d) T (Xh d)) = p ∧
          p ≤ V * (d + T + 1) ^ w) →
      ∀ (oc : ℕ → ℕ → ℕ → ℕ) (ec : ℕ → ℕ → ℕ),
        (∀ d n N, oc d n N ≤ A * (d + n + N + 1) ^ a) → (∀ d l, ec d l ≤ B * (d + l + 1) ^ b) →
      ∀ (d T κ : ℕ), 1 ≤ d → 1 ≤ κ → ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
      ∀ O : List (List Bool × Bool) → Gen, IsConsistentOracle (Fh d) O →
      ∀ f : Fin κ → Gen, (∀ j, f j ∈ Fh d) →
      ∀ hstar : Xh d → Bool, (∀ (j : Fin κ) (x : Xh d), e2e (f j) T x = hstar x) →
      ∀ (D : PMF (Xh d)) (P : Xh d → PMF (Fin κ)),
        (m5 d T κ ε δ : ℝ) ≤
            C * (d + T + κ + ⌈1 / ε⌉₊ + ⌈Real.log (1 / δ)⌉₊ + 2 : ℕ) ^ k ∧
        (iidSample (jointLaw D P) (m5 d T κ ε δ)).toOuterMeasure
            {s | ε < passErr D P T f (candSet T (alg5Fit O (knownObs T f s)))} ≤
          ENNReal.ofReal δ ∧
        ∀ s : Fin (m5 d T κ ε δ) → Xh d × Fin κ, ∀ x ∈ Xh d,
          (candSet T (alg5Fit O (knownObs T f s)) x).card ≤ κ ∧
          alg5Cost (oc d) (knownObs T f s) + candSetCost (ec d) T (alg5Fit O (knownObs T f s)) x ≤
            C * (d + T + κ + ⌈1 / ε⌉₊ + ⌈Real.log (1 / δ)⌉₊ + 2) ^ k := by sorry

end MultiThinkCoT.Supplement
