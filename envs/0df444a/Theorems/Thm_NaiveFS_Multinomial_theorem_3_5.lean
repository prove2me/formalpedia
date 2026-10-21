-- Prove2me | Theorems.Thm_NaiveFS_Multinomial_theorem_3_5
-- name    : NaiveFS.Multinomial.theorem_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:14:55.687334+00:00
-- url     : https://prove2.me/theorems/9a42616b-875f-4cf1-8a86-735342373760
-- title:
--   Theorem 3.5, p. 10 — duality-gap bound for separable problems: h_P(p̄) ≤ h_P(0)** + (m + 1) maxᵢ ρ(fᵢ), p̄ⱼ = (m + 1) maxᵢ ρ(gⱼᵢ)
-- statement:
--   Consider the separable problem (P) with $n\ge1$ blocks and $m$ constraints,
--   $$h_P(u)=\inf_{x_i\in\mathbb R^{d_i}}\Big\{\sum_{i=1}^nf_i(x_i)\ :\ \sum_{i=1}^ng_i(x_i)\le b+u\Big\},$$
--   where $g_{ji}$ denotes the $j$-th entry of $g_i$. Suppose every $f_i$ and every $g_{ji}$ ($i=1,\dots,n$, $j=1,\dots,m$) satisfies Assumption 3.3 (proper, 1-coercive, lower semicontinuous, with an affine minorant), and each lack of convexity $\rho(g_{ji})$ is finite. Let
--   $$\bar p_j=(m+1)\max_i\rho(g_{ji}),\qquad j=1,\dots,m.\qquad(22)$$
--   Then
--   $$h_P(\bar p)\le h_P(0)^{**}+(m+1)\max_i\rho(f_i).\qquad(23)$$
--
--   The paper quotes this result of Ekeland and Temam (after Aubin and Ekeland) and gives no proof; it is the Shapley–Folkman ingredient of the proof of Theorem 3.6, applied with $m=3$ constraints.
--
--   **Formalization Note** Functions take values in `EReal`; $f^{**}$ is the biconjugate and $\rho(f)=\sup_{\operatorname{dom}f}(f-f^{**})$. The finiteness of each $\rho(g_{ji})$ is added so that $\bar p\in\mathbb R^m$, which the page uses implicitly. The conjugate uses $\sup$ (the page prints $\inf$, see the definition item). The theorem is stated for (P) in general, not specialized to problem (25).
-- source:
--   Askari, d'Aspremont & El Ghaoui, Naive Feature Selection, arXiv:1905.09884v4, p. 10, Theorem 3.5 (22)–(23), citing Ekeland–Temam [6, Th. I.3]

import Mathlib
import Definitions.Def_NaiveFS_Multinomial_DualityGap

namespace NaiveFS.Multinomial

/-- Theorem 3.5, p. 10 (Ekeland–Temam [6, Th. I.3]). For problem (P) with `n ≥ 1` blocks and `m`
constraints, if every `fᵢ` and every coordinate `gⱼᵢ` satisfies Assumption 3.3 (and each
`ρ(gⱼᵢ)` is finite), then with `p̄ⱼ = (m + 1) maxᵢ ρ(gⱼᵢ)`,
`h_P(p̄) ≤ h_P(0)** + (m + 1) maxᵢ ρ(fᵢ)`. -/
theorem theorem_3_5 {n m : ℕ} (hn : 0 < n) {d : Fin n → ℕ}
    (f : ∀ i, (Fin (d i) → ℝ) → EReal) (g : ∀ i, (Fin (d i) → ℝ) → Fin m → EReal)
    (b : Fin m → ℝ)
    (hf : ∀ i, Assumption33 (f i)) (hg : ∀ i j, Assumption33 (fun x => g i x j))
    (hgρ : ∀ i j, lackOfConvexity (fun x => g i x j) ≠ ⊤) :
    hP f g b (fun j => ((m : ℝ) + 1) * (⨆ i, lackOfConvexity (fun x => g i x j)).toReal) ≤
      biconj (hP f g b) 0 + ((m : EReal) + 1) * ⨆ i, lackOfConvexity (f i) := by sorry

end NaiveFS.Multinomial
