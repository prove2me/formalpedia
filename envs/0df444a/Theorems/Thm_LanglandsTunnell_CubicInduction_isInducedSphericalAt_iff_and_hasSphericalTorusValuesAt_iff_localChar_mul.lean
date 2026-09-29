-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_isInducedSphericalAt_iff_and_hasSphericalTorusValuesAt_iff_localChar_mul
-- name    : LanglandsTunnell.CubicInduction.isInducedSphericalAt_iff_and_hasSphericalTorusValuesAt_iff_localChar_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/cbe62729-b1d3-56bc-b92a-96c82d5a00b9
-- title:
--   Unramified twist preserves spherical Hecke and torus conditions
-- statement:
--   Let $K$ be a field whose ring of integers is an integral $\mathcal{O}_{\mathbb{Q}}$-algebra, let $\chi$ be a homomorphism from the ideles $(\mathbb{A}_{\mathbb{Q}})^{\times}$ to $\mathbb{C}^{\times}$, and let $v$ be a height-one prime of $\mathcal{O}_{\mathbb{Q}}$ at which $\chi$ is unramified, in the sense that its local component `localChar` $\chi$ at $v$ (the composite of $\chi$ with the embedding of $(\mathbb{Q}_v)^{\times}$ into the ideles) takes the value $1$ on every unit $t$ of $\mathbb{Q}_v$ with both $t$ and $t^{-1}$ in the valuation ring. Let $c, c' : \mathrm{HeightOneSpectrum}(\mathcal{O}_K) \to \mathbb{C}$ satisfy $c'(w) = \chi(\varpi_v)^{f(w/v)} c(w)$ for every prime $w$ of $K$ lying under $v$, where $\varpi_v$ is the uniformizer idele at $v$ and $f(w/v)$ is the inertia degree `inertiaDeg'`. Let $W : \mathrm{GL}_3(\mathbb{Q}_v) \to \mathbb{C}$ and let $W'(g) = \mathrm{localChar}\,\chi\,v(\det g)\, W(g)$. The conclusion is a conjunction of two equivalences. First, $W$ satisfies `IsInducedSphericalAt` for $c$ at $v$ relative to the subgroup `localMaximalCompact3` of matrices whose entries and whose inverse's entries all have valuation $\le 1$ — that is, $W$ is right invariant under that subgroup, is a Hecke coset eigenfunction for $\mathrm{diag}(\varpi_v,1,1)$ with eigenvalue $N(v)\cdot \mathrm{inducedE1}(c,v)$ and for $\mathrm{diag}(\varpi_v,\varpi_v,1)$ with eigenvalue $N(v)\cdot \mathrm{inducedE2}(c,v)$ (the sum of $W$ over any finite system of coset representatives equals the eigenvalue times $W$), and satisfies $W(\mathrm{diag}(\varpi_v,\varpi_v,\varpi_v)\,g) = \mathrm{inducedE3}(c,v)\,W(g)$ — if and only if $W'$ satisfies the same conditions with $c$ replaced by $c'$. Second, $W$ satisfies `HasSphericalTorusValuesAt` for $c$ at $v$, i.e. $W(\mathrm{iotaTorusLocal}\,v\,n) = N(v)^{-n} S(n)$ for all $n$ and $W(\mathrm{twoRowPointLocal}\,v\,k_1\,(k_2+1)) = N(v)^{-k_1}\bigl(S(k_1)S(k_2+1) - S(k_1+1)S(k_2)\bigr)$ whenever $k_2+1 \le k_1$, where $N(v)$ is the absolute norm of $v$ and $S$ is the sequence determined by $S(0)=1$, $S(1)=e_1$, $S(2)=e_1^2-e_2$, $S(n+3)=e_1S(n+2)-e_2S(n+1)+e_3S(n)$ with $e_i = \mathrm{inducedE}i(c,v)$, if and only if $W'$ satisfies the corresponding identities with the $e_i$ formed from $c'$.
--
--   This is the local compatibility at a finite prime between twisting a $\mathrm{GL}_3$ Whittaker-type function by an unramified idele class character and rescaling the Hecke data of the cubic induction by the character's value at the uniformizer. It is used in the construction of the twisted cubic-induction package, being cited by [`LanglandsTunnell.CubicInduction.hasSphericalTorusValuesAt_twist_det_of_isUnramifiedCharAt`](thm.html#LanglandsTunnell.CubicInduction.hasSphericalTorusValuesAt_twist_det_of_isUnramifiedCharAt) and by [`LanglandsTunnell.CubicInduction.exists_isCubicInductionDataOn_arch_torusValues_localPackage_bad`](thm.html#LanglandsTunnell.CubicInduction.exists_isCubicInductionDataOn_arch_torusValues_localPackage_bad).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_isInducedSphericalAt_iff_and_hasSphericalTorusValuesAt_iff_localChar_mul.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.RankinSelberg

theorem LanglandsTunnell.CubicInduction.isInducedSphericalAt_iff_and_hasSphericalTorusValuesAt_iff_localChar_mul
    (K : Type) [Field K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 ℚ)) (hχ : IsUnramifiedCharAt χ v)
    (c c' : HeightOneSpectrum (𝓞 K) → ℂ)
    (hc : ∀ w ∈ primeFibre ℚ K v,
      c' w = (χ (uniformizerIdele ℚ v) : ℂ) ^ (v.asIdeal.inertiaDeg' w.asIdeal) * c w)
    (W : LocalGL3 v → ℂ) :
    (IsInducedSphericalAt c v (localMaximalCompact3 (𝓞 ℚ) ℚ v) W ↔
      IsInducedSphericalAt c' v (localMaximalCompact3 (𝓞 ℚ) ℚ v)
        (fun g => (localChar χ v (Matrix.GeneralLinearGroup.det g) : ℂ) * W g)) ∧
    (HasSphericalTorusValuesAt c v W ↔
      HasSphericalTorusValuesAt c' v (fun g => (localChar χ v (Matrix.GeneralLinearGroup.det g) : ℂ) * W g)) := by sorry
