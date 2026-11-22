-- Prove2me | Theorems.Thm_MasulloRH_theta_gram_witness_coefficient_growth
-- name    : MasulloRH.theta_gram_witness_coefficient_growth
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T23:46:16.372823+00:00
-- url     : https://prove2.me/theorems/152902f9-bd55-4015-b91f-30da03d710fa
-- title:
--   Forced weighted coefficient growth for rational theta Gram witnesses
-- statement:
--   Use the actual theta seed and normalized Gaussian pulse in the published `MasulloRH_GaussianThetaApproximation` definition:
--
--   $$\theta(x)=\sum_{k\in\mathbb Z}\bigl(e^{-\pi k^2e^{2x}}-3e^{-4\pi k^2e^{2x}}+2e^{-16\pi k^2e^{2x}}\bigr),\qquad p_T(x)=\frac{T+1}{\sqrt\pi}e^{-(T+1)^2x^2}.$$
--
--   There exist constants $C>0$ and $M\in\mathbb N$, independent of the height, number of terms, coefficients and shifts, with the following property. Let $n\ge2$, let $k=n+1$, $\delta=1/(16k)$, and $\tau=k\sqrt{2\log k}$. Choose any finite rational complex coefficients $a_i=a_{i,1}+i a_{i,2}$ and rational shifts $y_i$. Form the exact augmented system $u=(p_n,\theta(\cdot-y_0),\ldots)$ and signed coefficient vector $d=(1,-a_0,\ldots)$.
--
--   If its actual Hermitian Gram quadratic form satisfies
--
--   $$\operatorname{Re}\sum_{i,j}\overline{d_i}d_j\int_{\mathbb R}e^{3x/2+2(1/4-\delta)|x|}\overline{u_i(x)}u_j(x)\,dx<\frac\delta2,$$
--
--   then the weighted coefficient mass obeys
--
--   $$\sum_i |a_i|e^{3y_i/4}>\frac{e^{\pi\tau/4}}{2C\sqrt{k}(1+\tau)^M}.$$
--
--   All Gram entries and the actual weighted residual energy are integrable; this is proved from the registered theta-tail estimate within the proof, rather than included as an unchecked premise. The Gram form is exactly the energy of $p_n-\sum_i a_i\theta(\cdot-y_i)$, including its cross terms. The rational quantifiers, pulse, asymmetric weight and strict Gram margin are those of the cofinal Gram frontier.
--
--   This is a necessary conditioning bound on any such witness. It does not assert that witnesses exist, disprove their existence, or close the cofinal frontier. The mass includes the shift factor $e^{3y_i/4}$; with unrestricted shifts it is not a lower bound on the unweighted coefficient sum. Its proof uses the exact Gaussian and theta transforms, a weighted Cauchy–Schwarz bound, and independently proved classical Gamma and zeta growth estimates. It uses no Riemann-hypothesis conclusion or automatic vanishing of Gaussian divisor moments.
-- source:
--   New supporting result developed for the independent weighted-theta/Gram frontier b2ce922d-3f53-4192-b8a7-484fcd931614 of the Prove2Me Masullo RH specialization mission. The coefficient-growth argument is an independent consequence of the actual transform and weight. Elementary Mellin change-of-variable, Gaussian-transform and finite Gram-integration helpers are adapted with attribution from marozols accepted submission 5b2cbfbc-22d8-4073-bb0e-dbecd2699cb3 for theorem 8481aa5d-a121-4938-8de2-17c814da37b2; all needed helpers are supplied in this proof. The registered Gamma theorem e820e6f6 is classical FLT-library background (Anthropic fermats-last-theorem commit aa2d8b34692b16c70f699536de0d8e75b9a3e9ef), not an import of an Alpoge RH proof. This result is not attributed to a Masullo manuscript passage.

import Mathlib
import Definitions.Def_MasulloRH_GaussianThetaApproximation
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators ComplexConjugate
open MasulloRH.GaussianApproximation

theorem MasulloRH.theta_gram_witness_coefficient_growth :
    ∃ (C : ℝ) (M : ℕ), 0 < C ∧ ∀ (n m : ℕ), 2 ≤ n →
      ∀ (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ),
      let k : ℝ := (n:ℝ)+1
      let δ : ℝ := 1/(16*k)
      let u : Fin (m+1) → ℝ → ℂ := Fin.cons (pulse n)
        (fun i x => theta (x-(y i:ℝ)))
      let d : Fin (m+1) → ℂ := Fin.cons 1
        (fun i => -(((a i).1:ℂ)+((a i).2:ℂ)*Complex.I))
      let τ : ℝ := k*Real.sqrt (2*Real.log k)
      (∑ i, ∑ j, conj (d i)*d j*
        (∫ x : ℝ, (Real.exp (2*(3/4)*x+2*(1/4-δ)*|x|):ℂ)*conj (u i x)*u j x)).re < δ/2 →
      Real.exp ((Real.pi/4)*τ)/(2*C*Real.sqrt k*(1+τ)^M) <
        ∑ i, ‖((a i).1:ℂ)+((a i).2:ℂ)*Complex.I‖*Real.exp ((3/4)*(y i:ℝ)) := by sorry
