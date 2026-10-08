-- Prove2me | Theorems.Thm_LogGammaPolymer_Variance_theorem_3_3
-- name    : LogGammaPolymer.Variance.theorem_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:21:53.007263+00:00
-- url     : https://prove2.me/theorems/204b75ad-3475-4478-b734-93b9f8aa9fc8
-- title:
--   Theorem 3.3 — Burke property: edge and interior variables of a down-right path are independent inverse gammas
-- statement:
--   Assume (2.4) with $0<\theta<\mu$, and let $U_{i,j},V_{i,j},X_{i,j}$ be computed from the environment by the recursion (3.2). Let $z=(z_k)_{k\in\mathbb Z}$ be the down-right path in $\mathbb Z_+^2$ that comes down the $y$-axis to $(0,a)$, follows a given sequence of $b$ east steps $e_1$ and $a$ south steps $-e_2$ to $(b,0)$, and then runs along the $x$-axis. Let $T_{f_k}$ be its edge variables ($U_{z_k}$ on a horizontal edge, $V_{z_{k-1}}$ on a vertical edge) and $\mathcal I$ its interior. Then the variables $\{T_{f_k},X_z: k\in\mathbb Z,\ z\in\mathcal I\}$ are mutually independent with marginals
--   $$U^{-1}\sim\mathrm{Gamma}(\theta,1),\qquad V^{-1}\sim\mathrm{Gamma}(\mu-\theta,1),\qquad X^{-1}\sim\mathrm{Gamma}(\mu,1)\qquad(3.7),$$
--   that is, horizontal edge variables have the $U$-law, vertical edge variables the $V$-law, and interior variables the $X$-law.
--
--   In particular each ratio $U_{m,n}=Z_{m,n}/Z_{m-1,n}$ and $V_{m,n}=Z_{m,n}/Z_{m,n-1}$ has the law of a boundary weight. This is what makes the mean (2.5) and the variance identity (3.18) exact.
--
--   **Formalization Note** The paper states the result for every bi-infinite down-right path. It is formalized for the paths that coincide with the axes outside a finite portion. These are the paths of the first part of the paper's proof, and the paper's last paragraph of the proof reduces the general case to them (a finite subfamily lies inside a square $B$, where the path can be modified to meet the axes). The index set consists of the $a+b$ edges of the finite portion, the interior points, and the axis edges beyond $(b,0)$ and above $(0,a)$.
-- source:
--   Seppäläinen, Scaling for a one-dimensional directed polymer with boundary conditions, arXiv:0911.2446v4, Theorem 3.3, (3.7), p. 13; definitions of z, T, I on p. 12

import Mathlib
import Definitions.Def_LogGammaPolymer_Variance_Paths
import Definitions.Def_LogGammaPolymer_Variance_Environment
open MeasureTheory ProbabilityTheory

namespace LogGammaPolymer.Variance

theorem theorem_3_3 {θ μ : ℝ} (hθ : 0 < θ) (hθμ : θ < μ) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (E : Env θ μ P) (a b : ℕ) (s : Steps b a) :
    iIndepFun (fun t : BurkeIndex a b s => fun ω => burkeFamily (E.conf ω) a b s t) P ∧
    (∀ r : Fin (b + a), s.1 r = true →
      P.map (fun ω => (edgeVar (E.conf ω) a s.1 r)⁻¹) = gammaMeasure θ 1) ∧
    (∀ r : Fin (b + a), s.1 r = false →
      P.map (fun ω => (edgeVar (E.conf ω) a s.1 r)⁻¹) = gammaMeasure (μ - θ) 1) ∧
    (∀ p ∈ drInterior a s.1, P.map (fun ω => (X (E.conf ω) p.1 p.2)⁻¹) = gammaMeasure μ 1) ∧
    (∀ i : ℕ, b < i → P.map (fun ω => (U (E.conf ω) i 0)⁻¹) = gammaMeasure θ 1) ∧
    (∀ j : ℕ, a < j → P.map (fun ω => (V (E.conf ω) 0 j)⁻¹) = gammaMeasure (μ - θ) 1) := by sorry

end LogGammaPolymer.Variance
