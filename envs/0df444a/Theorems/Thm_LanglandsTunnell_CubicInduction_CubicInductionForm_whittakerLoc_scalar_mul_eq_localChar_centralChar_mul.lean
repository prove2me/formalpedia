-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_CubicInductionForm_whittakerLoc_scalar_mul_eq_localChar_centralChar_mul
-- name    : LanglandsTunnell.CubicInduction.CubicInductionForm.whittakerLoc_scalar_mul_eq_localChar_centralChar_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/d4c8a4ff-ceb6-535b-8f74-cf57d65b8fb4
-- title:
--   Local Whittaker functions scale by the local central character
-- statement:
--   Let $K$ be a number field, equipped with an algebra structure of $\mathcal O_{\mathbb Q}=\mathbb Z$ on $\mathcal O_K$ that is integral; let $\mathrm{pins}$ be a `CarrierPins` datum for $\mathbb Q$, i.e. a bundle consisting of a measurable space and a measure on $\mathrm{GL}_2(\mathbb A_{\mathbb Q})$, a subset $D$ of that group, a subgroup $Z$ of the idèles, a family of subgroups indexed by ideals of $\mathbb Z$, a family of adelic matrices indexed by the finite places, and a measurable space and measure on $\mathbb A_{\mathbb Q}$. Let $\psi$ be an additive character of $\mathbb A_{\mathbb Q}$ with values in $\mathbb C$, and $\mu$ a homomorphism from the idèles of $K$ to $\mathbb C^\times$, and assume that the set of finite places $v$ of $\mathbb Q$ that are bad for $(K,\mu)$ — those ramified in $K$ or twist-ramified above — is finite. Let $F$ be a cubic induction form for $(K,\mathrm{pins},\psi,\mu)$: a bundle consisting of a function `form` on $\mathrm{GL}_3(\mathbb A_{\mathbb Q})$, a global Whittaker function, local Whittaker functions `whittakerLoc` $v$ on $\mathrm{GL}_3(\mathbb Q_v)$ for each finite place $v$, an archimedean Whittaker function, a central character `centralChar` on the idèles, a dual Whittaker function, together with the axioms that `form` is left invariant under $\mathrm{GL}_3(\mathbb Q)$, transforms under central idelic scalars by `centralChar`, that `centralChar` is trivial on $\mathbb Q^\times$, cuspidality along the two maximal parabolics, the identification of the Whittaker function with the unipotent integral of `form`, the $\psi$-Whittaker transformation laws globally and locally, the mirabolic expansion summing to `form`, factorisability of the Whittaker function as the archimedean factor times the finite local factors over any finite set of places containing the bad ones at which the remaining components are integral, induced-spherical behaviour at good places, level invariance, local multiplicity one, moderate growth, $K$-finiteness, and further analytic conditions. Assume `F.form` $\neq 0$, and let $p$ be a finite place of $\mathbb Q$. Then for every unit $t$ of the completion $\mathbb Q_p$ and every $h \in \mathrm{GL}_3(\mathbb Q_p)$, the local Whittaker function of $F$ at $p$ satisfies $W_{F,p}(t\cdot I_3 \cdot h) = \omega_p(t)\,W_{F,p}(h)$, where $\omega_p$ is the local component at $p$ of `F.centralChar`, obtained by composing it with the inclusion of $\mathbb Q_p^\times$ into the idèle class group of $\mathbb Q$.
--
--   This records that the centre of $\mathrm{GL}_3(\mathbb Q_p)$ acts on the local Whittaker function of a cubic induction form through the local component of its central character, the local form of the central-character law for automorphic forms on $\mathrm{GL}_3$. It is used in the analysis of the local zeta integrals attached to such a form, in particular in the results on cyclic subspaces and functional equations at the bad places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_CubicInductionForm_whittakerLoc_scalar_mul_eq_localChar_centralChar_mul.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.CubicInductionForm.whittakerLoc_scalar_mul_eq_localChar_centralChar_mul
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (pins : CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hbad : {v : HeightOneSpectrum (𝓞 ℚ) | IsBadPlace K μ v}.Finite)
    (F : CubicInductionForm K pins ψ μ) (hF : F.form ≠ 0)
    (p : HeightOneSpectrum (𝓞 ℚ)) :
    ∀ (t : (p.adicCompletion ℚ)ˣ) (h : LocalGL3 p),
      F.whittakerLoc p (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) =
        ((NumberField.TateGlobal.localChar F.centralChar p t : ℂˣ) : ℂ) * F.whittakerLoc p h := by sorry
