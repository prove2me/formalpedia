-- Prove2me | Theorems.Thm_ModularCurve_eisensteinNumerator_dvd_mul_of_witness
-- name    : ModularCurve.eisensteinNumerator_dvd_mul_of_witness
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/1ebe948c-e96c-5c38-9208-efd3a8996ede
-- title:
--   Eisenstein numerator divides m z₀ for eta-quotient roots
-- statement:
--   Fix a natural number $\ell$ with $\ell \neq 0$ and $2 \le \ell$. Let $a, d$ be integers and $c'$ a positive natural number with $a d \equiv 1 \pmod{\ell c'}$, and let $z_0$ be an integer satisfying the rational identity $$12\Big(\frac{(a+d)(1-\ell)}{12\,\ell c'} + s(d, c') - s(d, \ell c')\Big) = \gcd(\ell - 1, 12)\, z_0,$$ where $s(h,k) = \sum_{r=0}^{k-1} (\!(r/k)\!)\,(\!(hr/k)\!)$ is the Dedekind sum built from the sawtooth function $(\!(x)\!)$, equal to $\{x\} - 1/2$ when $\{x\} \neq 0$ and to $0$ otherwise. Let $m$ be a natural number and $H : \mathbb{H} \to \mathbb{C}$ a continuous function on the upper half-plane such that $H(\tau)^{\ell - 1} = \big(\Delta(\tau)/\Delta(\ell\tau)\big)^m$ for all $\tau$, the scaling $\tau \mapsto \ell\tau$ being given by the action of the upper triangular matrix $\begin{pmatrix}\ell & 0\\ 0 & 1\end{pmatrix}$ in $\mathrm{GL}_2(\mathbb{R})$, and such that $H(\gamma \cdot \tau) = H(\tau)$ for every $\gamma \in \Gamma_0(\ell)$ and every $\tau$. Then the integer $(\ell - 1)/\gcd(\ell - 1, 12)$, the quotient being computed in $\mathbb{N}$, divides $m z_0$.
--
--   This is the unconditional form of Ogg's eta-quotient argument, as used by Mazur in his study of the Eisenstein ideal: the transformation law of $\log \eta$ along a matrix with lower row determined by the witness data $(a, d, c')$ constrains the existence of an $(\ell-1)$-st root of $(\Delta(\tau)/\Delta(\ell\tau))^m$ on $\Gamma_0(\ell)$. It is applied in [`ModularCurve.sharpUnitNecessary_of_mod_oneTwenty_eq_one_or_fortyNine`](thm.html#ModularCurve.sharpUnitNecessary_of_mod_oneTwenty_eq_one_or_fortyNine), where witnesses with suitable $z_0$ turn the conclusion into a divisibility condition on $m$ alone.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_eisensteinNumerator_dvd_mul_of_witness.lean

import Definitions.Def_ModularCurve_EtaQuotient
import Definitions.Def_NumberTheory_DedekindSum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.eisensteinNumerator_dvd_mul_of_witness (ℓ : ℕ) [NeZero ℓ] (hℓ : 2 ≤ ℓ) (a d : ℤ) (c' : ℕ) (hc' : 0 < c') (h1 : Int.ModEq ((ℓ * c' : ℕ) : ℤ) (a * d) 1) (z₀ : ℤ) (hδ : 12 * (((a + d : ℤ) : ℚ) * (1 - (ℓ : ℚ)) / (12 * ((ℓ * c' : ℕ) : ℚ)) + dedekindSum d c' - dedekindSum d (ℓ * c')) = ((Nat.gcd (ℓ - 1) 12 : ℕ) : ℚ) * z₀) (m : ℕ) (H : UpperHalfPlane → ℂ) (hH : Continuous H) (hpow : ∀ τ : UpperHalfPlane, H τ ^ (ℓ - 1) = (ModularForm.discriminant τ / ModularForm.discriminant (ModularForm.heckeDiagMatrix ℓ • τ)) ^ m) (hinv : ∀ γ ∈ CongruenceSubgroup.Gamma0 ℓ, ∀ τ : UpperHalfPlane, H (γ • τ) = H τ) : (ModularCurve.eisensteinNumerator ℓ : ℤ) ∣ (m : ℤ) * z₀ := by sorry
