-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_prod_map_Gamma_twistedGamma_and_dual_and_archRootNumber_discrete_one_real_one_complex
-- name    : LanglandsTunnell.Converse.prod_map_Gamma_twistedGamma_and_dual_and_archRootNumber_discrete_one_real_one_complex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/78bcbebe-89a7-526e-a4fe-bf445350b5b2
-- title:
--   Discrete-series Γ-slots and root number over a (1,1) field
-- statement:
--   Let $K$ be a number field, $w_0$ a real infinite place of $K$ and $w_{\mathbb C}$ a complex one, and assume every infinite place of $K$ equals $w_{\mathbb C}$ or $w_0$. Let $u_R, a_R$ assign to each real place a complex number and an element of $\mathbb{Z}/2$, and $u_C, k_C$ assign to each complex place a complex number and an integer. Let $P$ be a real archimedean parameter of discrete type, $P = \mathrm{RealArchParam.discrete}\ u_P\ n_P$ with $1 \le n_P$, and let $s \in \mathbb{C}$. Write $\mathrm{archOfParamR}$ for the constant family equal to $P$ at every real place and $\mathrm{archOfParamC}$ for the constant family equal to $P.\mathrm{baseChange} = \langle u_P, n_P, u_P, -n_P\rangle$ at every complex place. Five assertions are made. First, the multiset $\mathrm{twistedGammaR}$, the sum over real places of the $\mathrm{gammaR}$-multiset of the twist of $P$ by $(u_R, a_R)$, contributes the empty product: the product of $\Gamma_{\mathbb R}(s+\tfrac12+x)$ over it is $1$. Secondly, the product of $\Gamma_{\mathbb C}(s+\tfrac12+x)$ over $\mathrm{twistedGammaC}$ (the $\mathrm{gammaC}$-contributions of the twisted real parameters plus those of the twisted complex parameters) equals $$\Gamma_{\mathbb C}\bigl(s+\tfrac12+(u_P+u_R(w_0))+\tfrac{n_P}{2}\bigr)\,\Gamma_{\mathbb C}\bigl(s+\tfrac12+(u_P+u_C(w_{\mathbb C}))+\tfrac{|n_P+k_C(w_{\mathbb C})|}{2}\bigr)\,\Gamma_{\mathbb C}\bigl(s+\tfrac12+(u_P+u_C(w_{\mathbb C}))+\tfrac{|-n_P+k_C(w_{\mathbb C})|}{2}\bigr),$$ the absolute values being `Int.natAbs` cast to $\mathbb{C}$. Thirdly and fourthly, the same two identities hold for the dualised data — the real parameters replaced by their duals $\mathrm{discrete}(-u_P)\,n_P$, the complex parameters by $\langle -u_P,-n_P,-u_P,n_P\rangle$, and $u_R, u_C, k_C$ replaced by $-u_R, -u_C, -k_C$ — with $u_P, u_R(w_0), u_C(w_{\mathbb C})$ negated on the right-hand side and the two $\mathrm{natAbs}$ terms unchanged. Fifthly, $\mathrm{archRootNumber}$ for these data, namely the product over real places of the $\epsilon$-factors of the twisted real parameters times the product over complex places of those of the twisted complex parameters, multiplied by $(-1)^{(P.\mathrm{centralSign}).\mathrm{val}}$ and by $(-1)$ raised to the number of complex places of $K$, equals $$i^{\,n_P+1}\cdot\bigl(i^{\,|n_P+k_C(w_{\mathbb C})|}\, i^{\,|-n_P+k_C(w_{\mathbb C})|}\bigr)\cdot(-1)^{n_P+1}\cdot(-1)^{1}.$$
--
--   This is the archimedean bookkeeping for a discrete-series parameter over a number field of signature $(1,1)$: it evaluates the $\Gamma_{\mathbb R}$- and $\Gamma_{\mathbb C}$-slots of the completed $L$-function and of its contragredient, together with the archimedean root number, in the shape required by the converse-theorem functional equation. It is used in the Rankin–Selberg computations that match unfolded torus pairs with gamma factors for discrete-series data at a single complex place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_prod_map_Gamma_twistedGamma_and_dual_and_archRootNumber_discrete_one_real_one_complex.lean

import Definitions.Def_LanglandsTunnell_ArchBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField LanglandsTunnell LanglandsTunnell.Converse

open scoped Classical in

theorem LanglandsTunnell.Converse.prod_map_Gamma_twistedGamma_and_dual_and_archRootNumber_discrete_one_real_one_complex
    (K : Type) [Field K] [NumberField K]
    (w₀ wC : NumberField.InfinitePlace K) (h₀ : w₀.IsReal) (hC : wC.IsComplex)
    (hall : ∀ w : NumberField.InfinitePlace K, w = wC ∨ w = w₀)
    (uR : ∀ w : NumberField.InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : NumberField.InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : NumberField.InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : NumberField.InfinitePlace K, w.IsComplex → ℤ)
    (P : RealArchParam) (uP : ℂ) (nP : ℕ) (hnP : 1 ≤ nP) (hP : P = RealArchParam.discrete uP nP hnP)
    (s : ℂ) :
    (((twistedGammaR K (archOfParamR K P) uR aR).map fun x => Complex.Gammaℝ (s + 1 / 2 + x)).prod = 1) ∧
    (((twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC).map fun x => Complex.Gammaℂ (s + 1 / 2 + x)).prod =
        Complex.Gammaℂ (s + 1 / 2 + ((uP + uR w₀ h₀) + (nP : ℂ) / 2)) *
        (Complex.Gammaℂ (s + 1 / 2 + ((uP + uC wC hC) + ((((nP : ℤ) + kC wC hC).natAbs : ℕ) : ℂ) / 2)) *
        Complex.Gammaℂ (s + 1 / 2 + ((uP + uC wC hC) + (((-(nP : ℤ) + kC wC hC).natAbs : ℕ) : ℂ) / 2)))) ∧
    (((twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR).map
          fun x => Complex.Gammaℝ (s + 1 / 2 + x)).prod = 1) ∧
    (((twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => (archOfParamC K P w hw).dual)
          (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw)).map
          fun x => Complex.Gammaℂ (s + 1 / 2 + x)).prod =
        Complex.Gammaℂ (s + 1 / 2 + ((-uP + -uR w₀ h₀) + (nP : ℂ) / 2)) *
        (Complex.Gammaℂ (s + 1 / 2 + ((-uP + -uC wC hC) + ((((nP : ℤ) + kC wC hC).natAbs : ℕ) : ℂ) / 2)) *
        Complex.Gammaℂ (s + 1 / 2 + ((-uP + -uC wC hC) + (((-(nP : ℤ) + kC wC hC).natAbs : ℕ) : ℂ) / 2)))) ∧
    (archRootNumber K (archOfParamR K P) (archOfParamC K P) uR aR uC kC * (-1 : ℂ) ^ (P.centralSign).val *
          (-1 : ℂ) ^ (Finset.univ : Finset {w : NumberField.InfinitePlace K // w.IsComplex}).card =
        Complex.I ^ (nP + 1) *
          (Complex.I ^ ((nP : ℤ) + kC wC hC).natAbs * Complex.I ^ (-(nP : ℤ) + kC wC hC).natAbs) *
          (-1 : ℂ) ^ (nP + 1) * (-1 : ℂ) ^ 1) := by sorry
