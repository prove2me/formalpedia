-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_hasSphericalTorusValuesAt_twist_det_of_isUnramifiedCharAt
-- name    : LanglandsTunnell.CubicInduction.hasSphericalTorusValuesAt_twist_det_of_isUnramifiedCharAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/52e907f7-c1e5-5c4d-aca5-e3b5a84305e9
-- title:
--   Unramified twist by χᵥ∘det preserves induced spherical data
-- statement:
--   Let $K$ be a number field whose ring of integers is an integral $\mathcal O_{\mathbb Q}$-algebra, let $\nu\colon(\mathbb A_K^\times)\to\mathbb C^\times$ be a character of the idele group of $K$, let $\chi_{\mathbb A}\colon(\mathbb A_{\mathbb Q}^\times)\to\mathbb C^\times$ be an admissible twist (an idele class character, continuous and unitary), let $v$ be a height-one prime of $\mathcal O_{\mathbb Q}$, and assume $\chi_{\mathbb A}$ is unramified at $v$, i.e. its local component `localChar` kills every $t\in(\mathbb Q_v)^\times$ with $t$ and $t^{-1}$ integral. Put $\mu:=\nu\cdot(\chi_{\mathbb A}\circ N)$, where $N$ is the idelic norm attached to `genuineBaseChange ℚ K`. Three assertions are made. First, $v$ is a bad place for $\mu$ exactly when it is for $\nu$; that is, `IsRamifiedIn K v` or `IsTwistRamifiedAbove K μ v` holds iff `IsRamifiedIn K v` or `IsTwistRamifiedAbove K ν v` does. Second, for every $W\colon\mathrm{GL}_3(\mathbb Q_v)\to\mathbb C$ having the normalised spherical torus values of the coefficient system $\mathfrak P\mapsto\nu(\varpi_{\mathfrak P})$ (set to $0$ where $\nu$ is ramified) at $v$ — the prescribed values $(c_v)^{-n}$ times `sphericalTorusValue` of the induced data $E_1,E_2,E_3$ at the torus points `iotaTorusLocal v n`, and the corresponding $2\times2$ determinantal expressions at the two-row points `twoRowPointLocal v k₁ (k₂+1)` for $k_2+1\le k_1$ — the function $x\mapsto\chi_{\mathbb A,v}(\det x)\,W(x)$ has those values for the coefficient system of $\mu$. Third, the same twisting preserves the full local spherical datum at $v$ relative to $\mu$: right invariance under the subgroup of matrices in $\mathrm{GL}_3(\mathbb Q_v)$ whose entries and whose inverse's entries have valuation $\le1$, the two coset Hecke eigenvalue identities with eigenvalues $c_v\,E_1$ and $c_v\,E_2$, and the central relation with scalar $E_3$.
--
--   This is the statement that twisting a spherical vector by an unramified idele class character composed with the determinant matches the twist of the inducing character by the norm: the induced Euler factor of $\mu$ at $v$ is that of $\nu$ with $X\mapsto\chi_{\mathbb A,v}(\varpi)X$, since $\mu(\varpi_{\mathfrak P})=\nu(\varpi_{\mathfrak P})\chi_{\mathbb A,v}(\varpi)^{f(\mathfrak P\mid v)}$. It supplies the local input at good places for the twisted cubic induction data, and is used in the construction of twisted cubic induction data and in the local zeta computations for the twisted forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_hasSphericalTorusValuesAt_twist_det_of_isUnramifiedCharAt.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal LanglandsTunnell LanglandsTunnell.Converse
open LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg

theorem LanglandsTunnell.CubicInduction.hasSphericalTorusValuesAt_twist_det_of_isUnramifiedCharAt
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (_hdeg : Module.finrank ℚ K = 3)
    (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (χA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (_hχA : LanglandsTunnell.Converse.IsAdmissibleTwist ℚ χA)
    (v : HeightOneSpectrum (𝓞 ℚ)) (_hχv : IsUnramifiedCharAt χA v) :
    (IsBadPlace K (ν * χA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) v ↔ IsBadPlace K ν v) ∧
    (∀ W : LocalGL3 v → ℂ, HasSphericalTorusValuesAt (inducedCoeff K ν) v W →
      HasSphericalTorusValuesAt (inducedCoeff K (ν * χA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)) v
        (fun x : LocalGL3 v => ((NumberField.TateGlobal.localChar χA v (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W x)) ∧
    (∀ W : LocalGL3 v → ℂ,
      IsInducedSphericalAt (inducedCoeff K ν) v (localMaximalCompact3 (𝓞 ℚ) ℚ v) W →
      IsInducedSphericalAt (inducedCoeff K (ν * χA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)) v (localMaximalCompact3 (𝓞 ℚ) ℚ v)
        (fun x : LocalGL3 v => ((NumberField.TateGlobal.localChar χA v (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W x)) := by sorry
