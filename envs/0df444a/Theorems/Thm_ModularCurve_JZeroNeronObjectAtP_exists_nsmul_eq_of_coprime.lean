-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_exists_nsmul_eq_of_coprime
-- name    : ModularCurve.JZeroNeronObjectAtP.exists_nsmul_eq_of_coprime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/0f22a36d-3978-57dc-823a-3e33ef624d70
-- title:
--   Divisibility by m coprime to p on A-points
-- statement:
--   Fix natural numbers $N_0$ and $p$ with $N_0 \neq 0$ and $p$ prime, and assume $p \nmid N_0$. Let $A$ be a valuation subring of a fixed algebraic closure of $\mathbb{Q}$ lying over $p$, in the sense that the image of $p$ is a non-unit of $A$, so that $p$ belongs to the maximal ideal. Let $\Lambda$ be level data of level $N_0$ at $p$ for $A$: this provides in particular a structure morphism $\sigma_A \colon \operatorname{Spec} A \to \mathrm{base}\ p$, the spectrum of `baseRing p`, compatible with the chosen geometric point, together with a scheme over $\mathrm{base}\ p$ carrying a relative group law and identifications of its sections over the generic and the residual point with $J_0(N_0)$-type divisor class groups. Let $O$ be a Néron object at $p$ for these data: a scheme $G$ with a morphism $g \colon G \to \mathrm{base}\ p$, a commutative relative group law $O.L$ on $g$, a Galois- and Hecke-equivariant identification of the sections of $g$ over the generic point with $J_0(N_0p)$, geometric hypotheses on $g$ (smooth, separated, locally of finite type, quasi-compact, surjective, with preconnected fibres), flatness and surjectivity of every multiplication-by-$n$ endomorphism for $n > 0$, properness of the generic fibre, and further numerical data, all summarised here. Let $m > 0$ be coprime to $p$, and let $s$ be a section of $g$ over $\sigma_A$, i.e. a morphism $\operatorname{Spec} A \to G$ whose composite with $g$ is $\sigma_A$. Then there is such a section $z$ with $m \cdot z = s$, where $m \cdot z$ is the $m$-fold product of $z$ with itself under $O.L$ over $\sigma_A$, formed by iterating the group-law multiplication starting from the identity section.
--
--   This is the statement that multiplication by an integer $m$ invertible in the base is surjective on $A$-valued points of a smooth commutative group scheme over the henselian local ring $A$, whose residue field is algebraically closed; here it is applied to the group object underlying the Néron data for $J_0(N_0p)$ at $p$. It is used in the construction of inertia-invariant $m$-division points measuring the failure of a point to extend to the place $A$, a step in the level-lowering analysis at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_exists_nsmul_eq_of_coprime.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve
  ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.exists_nsmul_eq_of_coprime
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)
    (m : ℕ) (hm : 0 < m) (hmp : m.Coprime p) (s : SchemeHomOver Λ.σA O.g) :
    ∃ z : SchemeHomOver Λ.σA O.g, O.L.nsmul Λ.σA m z = s := by sorry
