-- Prove2me | Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_arithmeticGalois_complexConjAlgEquiv_smul_pt
-- name    : ModularCurve.ComplexPlaceDictionaryOf.arithmeticGalois_complexConjAlgEquiv_smul_pt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/e99ea9fb-aa85-5467-b050-f2c23f7a170c
-- title:
--   Coefficientwise conjugation sends pt(τ) to pt(-τ̄)
-- statement:
--   Let $\Gamma$ be a subgroup of $\mathrm{SL}_2(\mathbb{Z})$ containing $T = \begin{pmatrix}1&1\\0&1\end{pmatrix}$, and let $F_0$ be an intermediate field of $\mathbb{Q} \subseteq \mathbb{Q}((q))$ which is assumed equal to [`ModularCurve.qExpFunctionFieldC ℚ Γ`](def/ModularCurve_X1.html#L101), the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by all quotients $p_f/p_g$ of integral $q$-expansions of modular forms of level $\Gamma$ and equal weight with $p_g \neq 0$. Let $D$ be a complex place dictionary for $(\Gamma, F_0)$, that is, a point map $\mathrm{pt}$ from the upper half-plane to the places of $\mathbb{C}F_0 =$ `laurentBaseChange ℂ F₀` (the subfield of $\mathbb{C}((q))$ generated over $\mathbb{C}$ by the coefficientwise image of $F_0$), a place being a valuation subring containing $\mathbb{C}$, proper and a principal ideal ring, together with a positive ramification index at each $\tau$, such that $\mathrm{pt}$ is $\Gamma$-invariant, membership of $x$ in the valuation ring of $\mathrm{pt}(\tau)$ is equivalent to local boundedness of $\|\mathrm{realizeOf}\ \Gamma\ x\|$ on punctured neighbourhoods of $\tau$, and the meromorphic order at $\tau$ of the realisation of $x \neq 0$ is the ramification index times $\mathrm{ord}_{\mathrm{pt}(\tau)}(x)$. Then for every $\tau$ in the upper half-plane, the semilinear automorphism `arithmeticGalois F₀` attached to complex conjugation on $\mathbb{C}$, acting on $\mathbb{C}F_0$ coefficientwise and on places by pointwise image of the valuation subring, carries $\mathrm{pt}(\tau)$ to $\mathrm{pt}(J \cdot \tau)$, where `UpperHalfPlane.J` acts as $\tau \mapsto -\bar\tau$.
--
--   This is the action of complex conjugation on the non-cuspidal complex points of the modular curve of level $\Gamma$, for the $\mathbb{Q}$-structure given by rational $q$-expansions: on $\Gamma \backslash \mathfrak{H}$ it is $z \mapsto -\bar z$. It is used in the identification of the degree-zero Picard group of the complex curve $X_H$ with a quotient by a period lattice, in both its plain and slashed forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ComplexPlaceDictionaryOf_arithmeticGalois_complexConjAlgEquiv_smul_pt.lean

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_PeriodHomPair
import Definitions.Def_GaloisRep_ComplexConjugation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.ComplexPlaceDictionaryOf.arithmeticGalois_complexConjAlgEquiv_smul_pt
    (Γ : Subgroup SL(2, ℤ)) (hT : ModularGroup.T ∈ Γ)
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (hF : F₀ = ModularCurve.qExpFunctionFieldC ℚ Γ)
    (D : ModularCurve.ComplexPlaceDictionaryOf Γ F₀) (τ : UpperHalfPlane) :
    ModularCurve.arithmeticGalois F₀ complexConjAlgEquiv • D.pt τ = D.pt (UpperHalfPlane.J • τ) := by sorry
