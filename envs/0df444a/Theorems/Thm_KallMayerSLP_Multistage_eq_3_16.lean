-- Prove2me | Theorems.Thm_KallMayerSLP_Multistage_eq_3_16
-- name    : KallMayerSLP.Multistage.eq_3_16
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:19:31.390993+00:00
-- url     : https://prove2.me/theorems/a75b8a3e-7d3d-4e78-b594-891d28b32b56
-- title:
--   (3.16) — joint convexity of $r_t$, $\Phi_t$ and Jensen\'s inequality
-- statement:
--   Let (3.10) satisfy Assumption 3.2. For every stage $t=2,\dots,T$, the function $r_t(z_{t-1};\widehat\zeta_t)$ is jointly convex in $(z_{t-1};\widehat\zeta_t)$, the function $\Phi_t(z_{t-1};\widehat\zeta_{t-1})$ is jointly convex in $(z_{t-1};\widehat\zeta_{t-1})$, and
--   $$
--   r_t\big(z_{t-1};\widehat\zeta_{t-1},\mathbb E[\xi_t]\big)\le\mathbb E_{\xi_t}\big[r_t(z_{t-1};\widehat\zeta_{t-1},\xi_t)\big]=\Phi_t(z_{t-1};\widehat\zeta_{t-1}).
--   $$
--
--   This Jensen inequality replaces the random vector by its mean, and it is the source of the lower bound.
--
--   **Formalization Note** Convexity is for extended-real-valued functions, on the product of all decision and realization coordinates.
--
--   Differences from the source:
--   - reading: Assumption 3.2: the A_tt complete fixed recourse matrices ∀t → complete recourse of A_tt for t = 2, …, T; reason: A_11 is not a recourse matrix, and the book's Example 3.1 calls a problem with a non-complete first stage complete fixed recourse; this is the weaker hypothesis, so the statement implies the ∀t one
--   - generalization: supp ℙ_{ξ_t} ⊆ Ξ^t → ξ_t ∈ Ξ^t almost surely; reason: the support inclusion implies the almost sure one, and they agree for closed Ξ^t, so the statement specializes to the source
--   - encoding: z_{t-1} and ζ̂_t as finite sequences → full families z and w, of which only the coordinates the book lists are used; reason: the same functions; unused coordinates have no effect
--   - generalization: if Φ_{t+1} is jointly convex, then r_t and Φ_t are jointly convex and (3.16) holds → r_t, Φ_t jointly convex and (3.16) for every t = 2, …, T, unconditionally; reason: the hypothesis holds by the book's own backward induction from Φ_{T+1} ≡ 0, so the statement implies the conditional one
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, (3.16), p.264 (PDF 273)

import Mathlib
import Definitions.Def_KallMayerSLP_Multistage_Assumption32
import Definitions.Def_KallMayerSLP_Multistage_rFn
import Definitions.Def_KallMayerSLP_Multistage_IsEConvex

namespace KallMayerSLP.Multistage

open MeasureTheory

/-- **Chapter 3, joint convexity and (3.16)** (Kall & Mayer, *Stochastic Linear Programming* (2005),
Chapter 3, (3.16), p.264, PDF 273): for every stage `t = 2, …, T`, `r_t(z_{t-1}; ζ̂_t)` is jointly
convex in `(z_{t-1}; ζ̂_t)`, `Φ_t(z_{t-1}; ζ̂_{t-1})` is jointly convex in `(z_{t-1}; ζ̂_{t-1})`, and by
Jensen's inequality `r_t(z_{t-1}; ζ̂_{t-1}, 𝔼[ξ_t]) ≤ 𝔼_{ξ_t}[r_t(z_{t-1}; ζ̂_{t-1}, ξ_t)] = Φ_t(z_{t-1}; ζ̂_{t-1})`.

**Formalization Note.** Joint convexity is on the whole product `(∀ τ, ℝ^{n_τ}) × (∀ s, ℝ^{r_s})`,
of which `r_t` and `Φ_t` only use the coordinates the book lists. `𝔼[ξ_t]` is the Bochner integral
`∫ ξ_t dP`, and `Function.update w t 𝔼[ξ_t]` is the point `(ζ̂_{t-1}, 𝔼[ξ_t])`. -/
theorem eq_3_16 {D : MSLP} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ξ : ∀ t, Ω → Fin (D.r t) → ℝ} {Ξ : ∀ t, Set (Fin (D.r t) → ℝ)}
    (hA : Assumption32 D P ξ Ξ) {t : ℕ} (ht₂ : 2 ≤ t) (ht : t ≤ D.T) :
    IsEConvex (fun p : (∀ τ, Fin (D.n τ) → ℝ) × (∀ s, Fin (D.r s) → ℝ) =>
        rFn D (fun t => P.map (ξ t)) t p.1 p.2) ∧
      IsEConvex (fun p : (∀ τ, Fin (D.n τ) → ℝ) × (∀ s, Fin (D.r s) → ℝ) =>
        Phi D (fun t => P.map (ξ t)) t p.1 p.2) ∧
      ∀ (z : ∀ τ, Fin (D.n τ) → ℝ) (w : ∀ s, Fin (D.r s) → ℝ),
        rFn D (fun t => P.map (ξ t)) t z (Function.update w t (∫ ω, ξ t ω ∂P)) ≤
          Phi D (fun t => P.map (ξ t)) t z w := by sorry

end KallMayerSLP.Multistage
