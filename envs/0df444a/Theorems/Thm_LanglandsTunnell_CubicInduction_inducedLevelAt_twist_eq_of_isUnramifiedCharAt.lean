-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_inducedLevelAt_twist_eq_of_isUnramifiedCharAt
-- name    : LanglandsTunnell.CubicInduction.inducedLevelAt_twist_eq_of_isUnramifiedCharAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/9d4d6143-1206-5608-90b5-cc0b43636c73
-- title:
--   Unramified twist preserves induced level and K₁(vᶜ)-invariance
-- statement:
--   Let $K$ be a number field equipped with an algebra structure of $\mathcal O_{\mathbb Q}$ on $\mathcal O_K$ that is integral, and assume $[K:\mathbb Q]=3$. Let $\nu$ be a homomorphism from the idele group of $K$ to $\mathbb C^\times$ and $\chi_{\mathbb A}$ one from the idele group of $\mathbb Q$, both admissible twists, i.e. trivial on the principal ideles (the image of $K^\times$, resp. $\mathbb Q^\times$), continuous, and of absolute value $1$ everywhere. Let $v$ be a height-one prime of $\mathcal O_{\mathbb Q}$ at which $\chi_{\mathbb A}$ is unramified, meaning that the local component $\mathrm{localChar}\,\chi_{\mathbb A}\,v$ takes the value $1$ on every unit $t$ of $\mathbb Q_v$ with both $t$ and $t^{-1}$ in the valuation ring. Put $\mu:=\nu\cdot(\chi_{\mathbb A}\circ N)$, where $N$ is the idelic norm homomorphism from the $K$-ideles to the $\mathbb Q$-ideles attached to the base change of adele rings along $\mathbb Q\subseteq K$. Then three assertions hold. First, for every prime $\mathfrak P$ of $\mathcal O_K$ lying in the fibre over $v$ (that is, with $\mathfrak P\cap\mathcal O_{\mathbb Q}=v$), the conductor exponents of the local components agree: $\mathrm{conductorExponentAt}\,K\,\mathfrak P$ of $\mathrm{localChar}\,\mu\,\mathfrak P$ equals that of $\mathrm{localChar}\,\nu\,\mathfrak P$, the conductor exponent being the infimum of those $c$ for which the character is trivial on the $c$-th higher unit group while being non-trivial on the $m$-th for every $m<c$. Secondly, the induced levels agree, $\mathrm{inducedLevelAt}\,K\,\mu\,v=\mathrm{inducedLevelAt}\,K\,\nu\,v$, where the induced level is the (finite) sum over the primes $\mathfrak P$ of the fibre of the inertia degree of $\mathfrak P$ over $v$ times the conductor exponent at $\mathfrak P$. Thirdly, for every $c\in\mathbb N$ and every function $W$ on $\mathrm{GL}_3(\mathbb Q_v)$ satisfying $W(gk)=W(g)$ for all $g$ and all $k$ in $\mathrm{congruenceK1}\,\mathcal O_{\mathbb Q}\,\mathbb Q\,v\,c$ — those $k$ in the maximal compact subgroup (all entries of $k$ and of $k^{-1}$ of valuation $\le 1$) whose bottom row satisfies $|k_{2,0}|,|k_{2,1}|\le q_v^{-c}$ and $|k_{2,2}-1|\le q_v^{-c}$ — the twisted function $x\mapsto \mathrm{localChar}\,\chi_{\mathbb A}\,v(\det x)\cdot W(x)$ satisfies the same invariance $W'(gk)=W'(g)$ for all such $k$ and all $g$.
--
--   This is the bookkeeping statement that twisting a cubic idele class character by an unramified character of the rational ideles, pulled back along the idelic norm, changes neither the local conductor exponents above $v$ nor the resulting induced level, and that the corresponding twist of a local Whittaker-type function by $\chi_v\circ\det$ preserves invariance under the mirabolic congruence subgroup $K_1(v^c)$. It is used in the construction of twisted cubic induction data and in the $\mathrm{GL}_3$ Rankin–Selberg estimates, where the level of the twisted form must be read off in terms of the twisted character.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_inducedLevelAt_twist_eq_of_isUnramifiedCharAt.lean

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

theorem LanglandsTunnell.CubicInduction.inducedLevelAt_twist_eq_of_isUnramifiedCharAt
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (_hdeg : Module.finrank ℚ K = 3)
    (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_hν : LanglandsTunnell.Converse.IsAdmissibleTwist K ν)
    (χA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (_hχA : LanglandsTunnell.Converse.IsAdmissibleTwist ℚ χA)
    (v : HeightOneSpectrum (𝓞 ℚ)) (_hχv : IsUnramifiedCharAt χA v) :
    (∀ 𝔓 ∈ primeFibre ℚ K v,
      LanglandsTunnell.TateLocal.conductorExponentAt K 𝔓 (localChar (ν * χA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓) =
        LanglandsTunnell.TateLocal.conductorExponentAt K 𝔓 (localChar ν 𝔓)) ∧
    inducedLevelAt K (ν * χA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) v = inducedLevelAt K ν v ∧
    (∀ (c : ℕ) (W : LocalGL3 v → ℂ),
      (∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ v c, ∀ g : LocalGL3 v, W (g * k) = W g) →
      ∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ v c, ∀ g : LocalGL3 v,
        (fun x : LocalGL3 v => ((NumberField.TateGlobal.localChar χA v (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W x) (g * k) =
          (fun x : LocalGL3 v => ((NumberField.TateGlobal.localChar χA v (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W x) g) := by sorry
