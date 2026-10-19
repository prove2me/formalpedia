-- Prove2me | Theorems.Thm_OAI_Erdos3_primePower_polynomial_image_characteristic_decay_s2
-- name    : OAI.Erdos3.primePower_polynomial_image_characteristic_decay_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:45:25.14205+00:00
-- url     : https://prove2.me/theorems/801e3497-384d-40c5-92e1-839c7c6c4944
-- title:
--   Characteristic function decay for the image of a p-adically shifted polynomial map modulo a prime power under a homogeneous rank condition
-- statement:
--   Let $V$ be a finite type, $s > 0$ a natural number, and $J_j$ ($j \in \operatorname{Fin} s$) finite types. Let $p, A, b, e$ be natural numbers with $p$ prime, and $C \ge 0$ a real number. For each $j \in \operatorname{Fin} s$ and $i \in J_j$ let $F_{j,i}$ be a multivariate polynomial in the variables $V$ with coefficients in $\mathbb{Z}/p^A$, of total degree at most $j+1$. Assume the following rank condition: for every natural number $B$ with $b < B \le A$, every $j \in \operatorname{Fin} s$, and every $\mathrm{row} : J_j \to \mathbb{Z}/p^B$ having at least one unit entry,
--   $$\texttt{primePowerHomogeneousRankProbability}\ p\ A\ B\ j\ \_\ (F_j)\ \mathrm{row} \le p^{-CB},$$
--   where (as defined by OpenAI) this is the probability, over a uniformly random $u : \operatorname{Fin} j \to V \to \mathbb{Z}/p^B$, that the linear row extracted (OpenAI's `polynomialLinearRow`) from the $j$-fold iterated difference along $u$ of the combination with coefficients $\mathrm{row}$ of the degree-$(j+1)$ homogeneous components of the $F_{j,i}$ reduced modulo $p^B$ is zero.
--
--   Let $r : V \to \mathbb{Z}/p^A$ and let $\chi$ be an additive character of $\prod_j (J_j \to \mathbb{Z}/p^A)$ with values in $\mathbb{C}$. Then
--   $$\Bigl\| \mathbb{E}_{x}\, \chi\Bigl( (j, i) \mapsto F_{j,i}\bigl(v \mapsto r(v) + p^e x(v)\bigr) \Bigr) \Bigr\| \le \bigl(p^{b+e}\bigr)^{\gamma \cdot \kappa} \cdot \operatorname{ord}(\chi)^{-\gamma},$$
--   where $x$ is uniform on $V \to \mathbb{Z}/p^A$ (this mean is `finiteImageCharacteristic` of the uniform weights), $\operatorname{ord}(\chi)$ is the order of $\chi$ in the group of additive characters (`orderOf χ`, as a real number), $\gamma$ = `modularRankDecayExponent s C` $= C / (2^s s!) / 2^s$, and $\kappa$ = `modularRankChargeFactor s` $= 4s \cdot 2^s s!$.
--
--   Lean: `OAI.Erdos3.primePower_polynomial_image_characteristic_decay_s2`, which states OpenAI's `OAI.Erdos3.primePower_polynomial_image_characteristic_decay` (in `lean/OAI/Combinatorics/Progressions/Polynomial/CRTPolynomialChargeBound.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B113` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Polynomial/CRTPolynomialChargeBound.lean (declaration OAI.Erdos3.primePower_polynomial_image_characteristic_decay)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B113

section

namespace OAI

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

theorem primePower_polynomial_image_characteristic_decay_s2
    {V : Type*} [Fintype V] {s : ℕ} (hs : 0 < s)
    {J : Fin s → Type*} [∀ j, Fintype (J j)]
    (p A b e : ℕ) [NeZero p] (hp : p.Prime) (C : ℝ) (hC : 0 ≤ C)
    (F : ∀ j, J j → MvPolynomial V (ZMod (p ^ A)))
    (hF : ∀ j i, (F j i).totalDegree ≤ j.val + 1)
    (hrank : ∀ (B : ℕ) (_ : b < B) (hBA : B ≤ A) (j : Fin s)
      (row : J j → ZMod (p ^ B)), (∃ i, IsUnit (row i)) →
      primePowerHomogeneousRankProbability p A B j.val hBA (F j) row ≤
        (p : ℝ) ^ (-C * B))
    (r : V → ZMod (p ^ A)) (χ : AddChar (∀ j, J j → ZMod (p ^ A)) ℂ) :
    ‖finiteImageCharacteristic (FiniteProbabilityWeights.uniform (V → ZMod (p ^ A)))
      (fun x j i => eval (fun v => r v + (p : ZMod (p ^ A)) ^ e * x v) (F j i)) χ‖ ≤
      ((p ^ (b + e) : ℕ) : ℝ) ^ (modularRankDecayExponent s C * modularRankChargeFactor s) *
        (orderOf χ : ℝ) ^ (-modularRankDecayExponent s C) := by
  sorry

end Erdos3

end OAI
end
