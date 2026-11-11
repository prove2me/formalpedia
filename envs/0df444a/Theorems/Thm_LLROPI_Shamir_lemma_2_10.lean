-- Prove2me | Theorems.Thm_LLROPI_Shamir_lemma_2_10
-- name    : LLROPI.Shamir.lemma_2_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:34:05.096618+00:00
-- url     : https://prove2.me/theorems/e10cf16b-57b1-4ae2-8ead-1db26b2ee769
-- title:
--   Lemma 2.10 (MDS generalized von Neumann) — $|\mathbb E_x\prod_iL_i(F_i(x))|\le\prod_{j\in J}\|L_j\|_{U^3}\prod_{i\notin J}\|L_i\|_\infty$ for $|J|\le(3k-n)/2$, also with affine shifts
-- statement:
--   Let $1\le k\le n$, and let $F_1,\dots,F_n:\mathbb F_p^k\to\mathbb F_p$ be linear maps such that $(F_i(x))_{i\in S}:\mathbb F_p^k\to\mathbb F_p^S$ is an isomorphism for every $k$-element $S\subseteq[n]$. Let $J\subseteq[n]$ satisfy
--   $$|J|\le\frac{3k-n}{2}.\qquad(2.7)$$
--   Then for arbitrary functions $L_1,\dots,L_n:\mathbb F_p\to\mathbb C$,
--   $$\Big|\mathbb E_{x\in\mathbb F_p^k}\prod_{i=1}^nL_i(F_i(x))\Big|\le\Big(\prod_{j\in J}\|L_j\|_{U^3}\Big)\Big(\prod_{i\in[n]\setminus J}\|L_i\|_\infty\Big).\qquad(2.8)$$
--   The same conclusion holds if each $F_i(x)$ is replaced by $F_i(x)+c_i$ for arbitrary $c_i\in\mathbb F_p$. Both clauses are stated.
--
--   Differences from the source:
--   - encoding: (F_i(x))_{i∈S} : F_p^k → F_p^S an isomorphism for every S ∈ ([n] choose k); ‖L‖_∞; ‖L‖_{U³} → the map x ↦ (F i x)_{i ∈ S} is bijective for every S with S.card = k; supNorm (max over F_p); ShamirLeak.gowersNorm 3; reason: a linear map is an isomorphism exactly when it is bijective; the norms are the paper's
-- source:
--   Sun, Wootters, Improved Local Leakage Resilience of Shamir Secret Sharing and Worst-Case Optimal Polynomial Intersection, arXiv:2610.12357 (held version, sha256 f154f5ce…), Lemma 2.10, (2.7)–(2.8), p. 24 (PDF 26)

import Mathlib
import Definitions.Def_ShamirLeak_gowersNorm
import Definitions.Def_LLROPI_Shamir_Fourier

namespace LLROPI.Shamir

/-- **Lemma 2.10 (MDS generalized von Neumann inequality)**, p. 24 (PDF 26). Let `1 ≤ k ≤ n` and
let `F₁, …, Fₙ : 𝔽_p^k → 𝔽_p` be linear maps such that `(Fᵢ(x))_{i ∈ S} : 𝔽_p^k → 𝔽_p^S` is an
isomorphism for every `k`-element `S ⊆ [n]`. Let `J ⊆ [n]` satisfy `|J| ≤ (3k − n)/2`. Then for
arbitrary `L₁, …, Lₙ : 𝔽_p → ℂ`,
`|E_{x ∈ 𝔽_p^k} ∏ᵢ Lᵢ(Fᵢ(x))| ≤ (∏_{j ∈ J} ‖L_j‖_{U³}) (∏_{i ∈ [n] ∖ J} ‖Lᵢ‖_∞)`.
The same conclusion holds if each `Fᵢ(x)` is replaced by `Fᵢ(x) + cᵢ` for arbitrary `cᵢ ∈ 𝔽_p`.
Sun, Wootters, arXiv:2610.12357 (held version, sha256 f154f5ce…), Lemma 2.10, (2.7)–(2.8),
p. 24 (PDF 26).

**Formalization Note.** Both clauses are stated (the linear one and the one with shifts `c`).
`‖·‖_{U³}` is the published `ShamirLeak.gowersNorm 3`, `‖·‖_∞` is `supNorm`. -/
theorem lemma_2_10 (p : ℕ) [Fact p.Prime] (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n)
    (F : Fin n → (Fin k → ZMod p) →ₗ[ZMod p] ZMod p)
    (hMDS : ∀ S : Finset (Fin n), S.card = k →
      Function.Bijective (fun x : Fin k → ZMod p => fun i : S => F i x))
    (J : Finset (Fin n)) (hJ : (J.card : ℝ) ≤ (3 * (k : ℝ) - n) / 2)
    (L : Fin n → ZMod p → ℂ) :
    ‖(∑ x : Fin k → ZMod p, ∏ i, L i (F i x)) / (p : ℂ) ^ k‖ ≤
        (∏ j ∈ J, ShamirLeak.gowersNorm 3 (L j)) * ∏ i ∈ Jᶜ, supNorm (L i) ∧
    ∀ c : Fin n → ZMod p,
      ‖(∑ x : Fin k → ZMod p, ∏ i, L i (F i x + c i)) / (p : ℂ) ^ k‖ ≤
        (∏ j ∈ J, ShamirLeak.gowersNorm 3 (L j)) * ∏ i ∈ Jᶜ, supNorm (L i) := by sorry

end LLROPI.Shamir
