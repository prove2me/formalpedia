-- Prove2me | Theorems.Thm_HaircutRate_Downside_proposition_2
-- name    : HaircutRate.Downside.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:57:34.706829+00:00
-- url     : https://prove2.me/theorems/44c5cc06-0699-49eb-864e-14c3477443dc
-- title:
--   Proposition 2, p. 20 (haircut clause in Gateaux form) — downside FOSD improvement lowers ω*, R and raises p; H falls iff (33)
-- statement:
--   Throughout, $\Omega=[\underline\omega,\bar\omega]$ with $0<\underline\omega<\bar\omega$, $K>0$ units of the risky asset paying $\omega$ in state $\omega$, depositors' endowments $0\le e^d_1<e^d_0$, and a utility $u$ of class $C^2$ on $(0,\infty)$ with $u'>0$ and $u''<0$ there. The payoff density $f$ is nonnegative and integrable on $\Omega$ with total mass $1$, $F(x)=\int_{\underline\omega}^{x} f$, and $\mathbb E[\varphi]=\int_{\underline\omega}^{\bar\omega}\varphi f$. Write $D=(e^d_0-e^d_1)/K$ and $q^{bp}(x)=\mathbb E\big[\tfrac{u'(e^d_1+K\min(\omega,x))}{u'(e^d_1+Kx)}\min(\omega,x)\big]$ for the bond pricing curve (23). A downside improvement direction $\psi$ at the pre-shock face value $\omega^*$ is an integrable function vanishing outside $(\underline\omega,\omega^*)$ with $\int_{\underline\omega}^{\omega^*}\psi=0$ and $\int_{\underline\omega}^{\omega^*}v\psi>0$ for every $v$ strictly increasing on $[\underline\omega,\omega^*]$; the shocked density is $f+\tau\psi$, and $\tau_0>0$ is such that $f+\tau\psi\ge 0$ on $\Omega$ for all $\tau\in[0,\tau_0]$.
--
--   Assume Assumption 2 ((20)–(21)) and Assumption 3 ((32)), let $\omega^*$ be the equilibrium face value of $f$, and write $\omega^*(\tau),R(\tau),p(\tau),H(\tau)$ for the face value, interest rate, asset price and haircut of $f+\tau\psi$. Then:
--
--   1. for every $\tau\in(0,\tau_0]$: $\omega^*(\tau)<\omega^*$, $R(\tau)<R(0)$ and $p(\tau)>p(0)$;
--   2. $\tau\mapsto H(\tau)$ has a right derivative $H'(0^+)$ at $\tau=0$, and
--   $$H'(0^+)<0\iff\int_{\omega^*}^{\bar\omega}\omega\,dF(\omega)>(1-F(\omega^*))\,\frac{e^d_0-e^d_1}{K},$$
--   which is condition (33), $\mathbb E[\omega\mid\omega>\omega^*]>(e^d_0-e^d_1)/K$, multiplied out.
--
--   An improvement in the downside quality of collateral thus lowers the face value and the interest rate and raises the asset price, while it lowers the haircut exactly when the upside is good enough relative to the scarcity of collateral.
--
--   **Formalization Note.** The haircut clause is posed as the sign of the right derivative at $\tau=0$, as in the paper's own derivation (34)–(35): for a finite shock the sign of the change in $H$ is not decided by (33) at the pre-shock face value, so the finite-shock "iff" is not posed. The face-value, rate and price clauses hold for every $\tau\in(0,\tau_0]$. Condition (33) is multiplied by $1-F(\omega^*)$; when that probability is $0$ both sides of the equivalence are false.
-- source:
--   Hao, The joint determination of haircuts and interest rates for collateralized loans in shadow banking, author's version of 19 Feb 2025 (sha256 924ec4ed…), Proposition 2, p. 20; shock f + τψ, (34), (35) and footnote 26, p. 22; footnote 23, p. 19

import Mathlib
import Definitions.Def_HaircutRate_Downside_Setting

namespace HaircutRate.Downside
open Set Economy

theorem proposition_2 (E : Economy) (hE : E.Valid) (hA3 : E.Assumption3)
    (f : ℝ → ℝ) (hf : E.IsDensity f) (hA2 : E.Assumption2 f)
    (ψ : ℝ → ℝ) (hψ : E.IsDownsideImprovement (E.faceValue f) ψ)
    (τ₀ : ℝ) (hτ₀ : 0 < τ₀)
    (hdens : ∀ τ ∈ Icc 0 τ₀, ∀ ω ∈ Icc E.lo E.hi, 0 ≤ shock f ψ τ ω) :
    (∀ τ ∈ Ioc 0 τ₀,
      E.faceValue (shock f ψ τ) < E.faceValue f ∧
      E.rate (shock f ψ τ) < E.rate f ∧
      E.assetPrice f < E.assetPrice (shock f ψ τ)) ∧
    ∃ d : ℝ, HasDerivWithinAt (fun τ => E.haircut (shock f ψ τ)) d (Ici 0) 0 ∧
      (d < 0 ↔ (1 - E.cdf f (E.faceValue f)) * E.D < ∫ ω in E.faceValue f..E.hi, ω * f ω) := by sorry

end HaircutRate.Downside
