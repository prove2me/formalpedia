-- Prove2me | Theorems.Thm_GraphNNSphere_Supplement_theorem_4_3
-- name    : GraphNNSphere.Supplement.theorem_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:52:19.067898+00:00
-- url     : https://prove2.me/theorems/709ad1ab-2ed8-4e64-8bdb-ab960f612636
-- title:
--   Theorem 4.3, p.30 — navigation with a sharper density bound near the query
-- statement:
--   Let $d=d(n)$ be in the dense regime and fix $k\ge1$, $\gamma>\gamma_c$, $0\le\kappa\le\kappa_0$ with $\kappa<h(\gamma)$, and $\kappa\le\bar\kappa<\gamma$. There is a finite $K_0=K_0(\gamma,\kappa,\bar\kappa)$ such that the following holds for every fixed $K\ge K_0$. Let $\Delta=\lceil e^{\gamma d}\rceil$ and let $P=f\,d\sigma_{d-1}$ be fixed before the data, with $f>0$ almost everywhere, $\log(1/\rho_{\min})=o(d)$ and
--
--   $$\operatorname*{ess\,osc}_{C(x,Ke^\gamma\rho(x))}\log f\le\bar\kappa d\qquad\text{for every }x\in S^{d-1}.$$
--
--   Let $Q_\kappa=\{q:\operatorname{ess\,osc}_{C(q,Ke^\gamma\rho(q))}\log f\le\kappa d\}$. Then $Q_\kappa$ is closed, hence Borel. For every absolutely continuous query law $Q$ fixed before the data, with probability at least $1-e^{-c_*d}$ there is a Borel set $B$ with $Q(B)\le e^{-c_*d}$ such that greedy navigation on $N_\Delta$ succeeds from every entry for every $q\in Q_\kappa\setminus B$; for every such $q$ and every entry the number of complete expansions is at most $H=O(1+\rho_{\min}^{-1})=e^{o(d)}$ and the evaluation cost is at most $1+\Delta H=e^{(\gamma+o(1))d}$. Here $c_*>0$ and the constant in $H$ depend only on $(\gamma,\kappa,\bar\kappa)$, and the threshold for large $n$ is independent of $Q$.
--
--   The theorem separates the density condition needed near the query (variation $e^{\kappa d}$, ruling out false local minima) from the weaker one needed to reach it from distant entries (variation $e^{\bar\kappa d}$); $\bar\kappa=\kappa$ gives Theorem 4.1(a).
--
--   **Formalization Note** $K_0$, $c_*$ and $C_H$ come right after $(\gamma,\kappa,\bar\kappa)$. Closedness of $Q_\kappa$ is asserted at every $n$ at which $f_n$ is a density positive almost everywhere.
--
--   Differences from the source:
--   - encoding: O(·), o(1), Ω(d), e^{o(d)}, "with probability 1 − o(1)", "for all sufficiently large n" → explicit constants and vanishing sequences in the quantifier order of §2.1 (fixed parameters, constants, d(·), vanishing sequences, ∀ᶠ n), probabilities as measures of explicit measurable events; reason: Lean convention, as in the published goal Theorem 3.1
--   - generalization: hypotheses on f (density, f > 0 a.e., local oscillation ≤ κ̄d at every x) for every n → required only for all large n; reason: the conclusion is asymptotic; a sequence with the properties for every n has them eventually
--   - generalization: "The set Q_κ is closed" (for the density of the theorem) → Q_κ is closed at every n at which f_n is a density with f_n > 0 a.e., without the oscillation and ρ_min hypotheses; reason: the paper asserts closedness for the fixed density satisfying all hypotheses, which is one of the instances covered; the closedness argument (ρ_f continuous when f > 0 a.e., caps exhausted by open caps) uses only positivity
--   - encoding: H = O(1 + ρ_min^{−1}) = e^{o(d)}, cost ≤ 1 + ΔH = e^{(γ+o(1))d} → H := C_H(1 + 1/ρ_min), expansions ≤ H ≤ e^{ε_n d}, evaluations ≤ 1 + ΔH ≤ e^{(γ+ε_n)d}; reason: explicit constant and vanishing sequence
--   - encoding: log(1/ρ_min) = o(d) → ρ_min ≥ e^{−ε_n d} with ε_n → 0; reason: equivalent since ρ_min ≤ π; avoids log(1/0) = 0
--   - encoding: measurable / Borel query sets → MeasurableSet on the sphere (the subtype of ℝ^d with its Borel σ-algebra); reason: same sets
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), Theorem 4.3, p.30 (PDF p.32); ρ(x), ρ_min §1.2, p.4 and §2.5, p.18

import Mathlib
import Definitions.Def_GraphNNSphere_IsNavGraph
import Definitions.Def_GraphNNSphere_maxDeg
import Definitions.Def_GraphNNSphere_greedyRun
import Definitions.Def_GraphNNSphere_W
import Definitions.Def_GraphNNSphere_nnGraph
import Definitions.Def_GraphNNSphere_gammaC
import Definitions.Def_GraphNNSphere_IsDenseRegime
import Definitions.Def_GraphNNSphere_Supplement_sampleLaw
import Definitions.Def_GraphNNSphere_Supplement_rhoF
import Definitions.Def_GraphNNSphere_Supplement_essOscLog
import Definitions.Def_GraphNNSphere_Supplement_hDense
import Definitions.Def_GraphNNSphere_Supplement_IsRegular

open MeasureTheory Filter Topology

namespace GraphNNSphere

namespace Supplement

/-- Theorem 4.3, navigation with a sharper density bound near the query (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), Theorem 4.3, p.30).
Dense regime, `γ > γ_c`, `0 ≤ κ ≤ κ₀`, `κ < h(γ)`, `κ ≤ κ̄ < γ`. There is `K₀ = K₀(γ, κ, κ̄)` such
that for every fixed `K ≥ K₀`: if `P = f dσ` with `f > 0` a.e., `log(1/ρ_min) = o(d)` and
`ess osc_{C(x, Ke^γ ρ(x))} log f ≤ κ̄ d` for every `x`, then
`Q_κ = {q : ess osc_{C(q, Ke^γ ρ(q))} log f ≤ κd}` is closed, and for every absolutely continuous
query law `Q`, with probability `≥ 1 - e^{-c* d}` there is a Borel `B` with `Q(B) ≤ e^{-c* d}` such that
greedy navigation on `N_Δ` succeeds from every entry for every `q ∈ Q_κ \ B`, with at most
`H = O(1 + ρ_min^{-1}) = e^{o(d)}` complete expansions and evaluation cost at most
`1 + ΔH = e^{(γ+o(1))d}`. `c*` and the constant in `H` depend only on `(γ, κ, κ̄)`, and the threshold in
`n` is independent of `Q`.

**Formalization Note** `K₀`, `c*` and `C_H` come right after `(γ, κ, κ̄)`, before `K` and `k`. The
large-`n` threshold comes before `Q`. The hypotheses on `f` are required for all large `n`;
`log(1/ρ_min) = o(d)` is `ρ_min ≥ e^{-ε_n d}` with `ε_n → 0`. Closedness of `Q_κ` is asserted for every
`n` at which `f_n` is a density with `f_n > 0` a.e. -/
theorem theorem_4_3 :
    ∀ γ κ κbar : ℝ, gammaC < γ → 0 ≤ κ → κ ≤ kappa0 → κ < hDense γ → κ ≤ κbar → κbar < γ →
      ∃ K₀ cstar CH : ℝ, 0 < cstar ∧ 0 < CH ∧
      ∀ K : ℝ, K₀ ≤ K → ∀ k : ℕ, 1 ≤ k →
      ∀ d : ℕ → ℕ, IsDenseRegime d →
      ∀ f : ∀ n, Sph (d n) → ℝ,
        (∀ᶠ n in atTop, IsDensity (d n) (f n) ∧ (∀ᵐ x ∂(unif (d n)), 0 < f n x) ∧
          ∀ x : Sph (d n), essOscLog (d n) (f n) (cap x (K * Real.exp γ * rhoF n (d n) (f n) x)) ≤
            ((κbar * (d n : ℝ) : ℝ) : EReal)) →
        (∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
          ∀ᶠ n in atTop, Real.exp (-(ε n * (d n : ℝ))) ≤ rhoMin n (d n) (f n)) →
        (∀ n, IsDensity (d n) (f n) → (∀ᵐ x ∂(unif (d n)), 0 < f n x) →
          IsClosed {q : Sph (d n) |
            essOscLog (d n) (f n) (cap q (K * Real.exp γ * rhoF n (d n) (f n) q)) ≤
              ((κ * (d n : ℝ) : ℝ) : EReal)}) ∧
        ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ n : ℕ in atTop,
          CH * (1 + 1 / rhoMin n (d n) (f n)) ≤ Real.exp (ε n * (d n : ℝ)) ∧
          1 + (⌈Real.exp (γ * (d n : ℝ))⌉₊ : ℝ) * (CH * (1 + 1 / rhoMin n (d n) (f n))) ≤
            Real.exp ((γ + ε n) * (d n : ℝ)) ∧
          ∀ Q : Measure (Sph (d n)), IsProbabilityMeasure Q → Q ≪ unif (d n) →
          ∃ E : Set (Fin n → Sph (d n)), MeasurableSet E ∧
            1 - Real.exp (-(cstar * (d n : ℝ))) ≤ (dataLawF n (d n) (f n) E).toReal ∧
            ∀ X ∈ E, ∃ B : Set (Sph (d n)), MeasurableSet B ∧
              (Q B).toReal ≤ Real.exp (-(cstar * (d n : ℝ))) ∧
              ∀ q : Sph (d n),
                essOscLog (d n) (f n) (cap q (K * Real.exp γ * rhoF n (d n) (f n) q)) ≤
                  ((κ * (d n : ℝ) : ℝ) : EReal) → q ∉ B →
                ∀ x₀ : Fin n, ∃ moves expansions evals : ℕ,
                  greedyRun (nnGraph X ⌈Real.exp (γ * (d n : ℝ))⌉₊) X q k x₀ =
                    .success moves expansions evals ∧
                  (expansions : ℝ) ≤ CH * (1 + 1 / rhoMin n (d n) (f n)) ∧
                  (evals : ℝ) ≤ 1 + (⌈Real.exp (γ * (d n : ℝ))⌉₊ : ℝ) *
                    (CH * (1 + 1 / rhoMin n (d n) (f n))) := by sorry

end Supplement

end GraphNNSphere
