-- Prove2me | Theorems.Thm_ModularCurve_ModularPolynomialData_separable_map_ratFunc_of_not_dvd
-- name    : ModularCurve.ModularPolynomialData.separable_map_ratFunc_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/f60318d3-4676-5e98-97f2-d63ac3697949
-- title:
--   Separability of Φ_N modulo a prime ℓ∤ N
-- statement:
--   Let $N$ be a nonzero natural number and let `data` be a modular polynomial datum of level $N$: a polynomial $\Phi \in \mathbb{Z}[X][Y]$ (an element of `Polynomial (Polynomial ℤ)`, the outer variable playing the role of $Y$) together with the three properties recorded in the structure, namely that $\Phi$ is monic as a polynomial in the outer variable, that its degree in that variable equals $\psi(N) = \sum_{d \mid N,\ d \text{ squarefree}} N/d$, and that evaluating the outer variable at the Laurent series $j(q^N)$ while sending each coefficient in $\mathbb{Z}[X]$ to its value under the ring homomorphism $X \mapsto j(q)$ into the Laurent series over $\mathbb{Q}$ gives $0$. Let $\ell$ be a prime with $\ell \nmid N$. The conclusion is that the polynomial obtained from $\Phi$ by reducing all integer coefficients into $K = \overline{\mathbb{F}}_\ell$, realised as `AlgebraicClosure (ZMod ℓ)` (that is, applying coefficientwise the map $\mathbb{Z}[X] \to K[X]$ induced by $\mathbb{Z} \to K$), and then mapping its coefficients along $K[X] \hookrightarrow K(X)$, is separable as an element of $K(X)[Y]$, i.e. it is coprime to its derivative. No assertion is made about irreducibility or about the number of roots.
--
--   This is the separability half of Igusa's theorem that the $j$-line map of $X_0(N)$ remains generically étale in characteristic $\ell$ for $\ell \nmid N$; the hypothesis $\ell \nmid N$ is essential. It is used in the construction of the Igusa scheme, specifically in the proofs that the tensored chart algebras [`ModularCurve.IgusaScheme.isReduced_chartAlgFin_tensor`](thm.html#ModularCurve.IgusaScheme.isReduced_chartAlgFin_tensor) and [`ModularCurve.IgusaScheme.isReduced_chartAlgInf_tensor`](thm.html#ModularCurve.IgusaScheme.isReduced_chartAlgInf_tensor) are reduced.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ModularPolynomialData_separable_map_ratFunc_of_not_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.ModularPolynomialData.separable_map_ratFunc_of_not_dvd (N : ℕ) [NeZero N] (data : ModularCurve.ModularPolynomialData N)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ N) :
    ((data.Φ.map (Polynomial.mapRingHom (Int.castRingHom (AlgebraicClosure (ZMod ℓ))))).map
      (algebraMap (Polynomial (AlgebraicClosure (ZMod ℓ))) (RatFunc (AlgebraicClosure (ZMod ℓ))))).Separable := by sorry
