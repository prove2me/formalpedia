-- Prove2me | Theorems.Thm_GabidulinProx_UniqueDecoding_Supplement_theorem_3_12
-- name    : GabidulinProx.UniqueDecoding.Supplement.theorem_3_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:46:11.468893+00:00
-- url     : https://prove2.me/theorems/6aeb1df5-2937-4a13-9378-de073f7387dd
-- title:
--   Theorem 3.12 — a line all $d/2$-close whose interleaving is $3d/4$-far
-- statement:
--   Let $K=\mathbb F_q$ be any finite field and $g\ge1$. Let $F=\mathbb F_{q^{6g}}$ and $n=6g$. Let $A=(\alpha_1,\dots,\alpha_n)$ be any $\mathbb F_q$-basis of $F$ and let $C=G(A,2g+1)\subseteq F^n$, whose distance is $d=n-k+1=4g$. Then there exist words $u_0,u_1\in F^n$ such that
--
--   $$\Pr_{\lambda\in F}\bigl[d(u_0+\lambda u_1,C)\le d/2\bigr]=1,$$
--
--   but
--
--   $$d([u_0,u_1],C^2)\ge d(u_1,C)\ge\tfrac{3d}4 .$$
--
--   With $d=4g$, the radii are $d/2=2g$ and $3d/4=3g$. This shows that correlated agreement fails at $e=d/2$ even when every point of the line is close.
--
--   Differences from the source:
--   - encoding: finite fields $\mathbb F_q\subseteq\mathbb F_{q^m}$ → finite fields $K,L$ with an algebra structure, $q=|K|$, $q^m=|L|$; reason: every finite extension of $\mathbb F_q$ has this form, and $|L|=|K|^{[L:K]}$
--   - encoding: rank after expanding each entry in a fixed $\mathbb F_q$-basis of $\mathbb F_{q^m}$ → $K$-dimension of the $K$-span of the columns (published `wordRank`, `codeDistance`, `pairDistance`); reason: the matrix rank does not depend on the chosen basis; the pair distance is the joint column rank of the $2m\times n$ matrix
--   - encoding: points $u_0+\lambda u_1$ with $\lambda$ uniform in $\mathbb F_{q^m}$ → parameters $z\in L$ with the published `linePoint` and `uniformFraction` (uniform over all of $L$, including $z=0$); reason: the line is the image of this parameterization and the probability is the counting measure normalized by $|L|$
--   - encoding: any $\mathbb F_q$-basis $A=\{\alpha_1,\dots,\alpha_n\}$ of the field and $C=G(A,k)$ → every $K$-linearly independent family $\alpha:\mathrm{Fin}\,n\to L$ with $[L:K]=n$ and the published `gabidulin K α k`; reason: $n$ independent vectors in an $n$-dimensional space form a basis; the published code is the image of the $q$-linearized evaluation map
--   - encoding: $d/2$ and $3d/4$ → the numbers $2g$ and $3g$; reason: the paper fixes $d=n-k+1=6g-(2g+1)+1=4g$ for Gabidulin codes
-- source:
--   Songsong Li, Chaoping Xing, Chen Yuan, Ruiqi Zhu, Proximity Gaps for Gabidulin Codes and Applications, STOC 2027 submission #434 (October 2026), §3.3 setting p.24 and Theorem 3.12 p.26; proof pp.26–27. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/434.pdf, SHA-256 8f644bcdfbdcd3478384d77d75a0f88ea116c29b14c52714f58bffb9ffda25cf

import Definitions.Def_GabidulinProx_UniqueDecoding_Supplement_Objects

namespace GabidulinProx.UniqueDecoding.Supplement

open GabidulinProx.UniqueDecoding

/-- Theorem 3.12, p.26: for every finite field `K` and `g ≥ 1`, with `F = F_{q^(6g)}`,
`n = 6g`, any `K`-basis `A` of `F` and `C = G(A, 2g+1)` (so `d = n - k + 1 = 4g`), there are
`u₀, u₁` with `Pr_z[d(u₀ + z u₁, C) ≤ d/2] = 1` but `d([u₀,u₁], C²) ≥ d(u₁, C) ≥ 3d/4`;
here `d/2 = 2g` and `3d/4 = 3g`. -/
theorem theorem_3_12 {K F : Type*} [Field K] [Fintype K] [Field F] [Fintype F] [Algebra K F]
    (g : ℕ) (hg : 1 ≤ g) (hdim : Module.finrank K F = 6 * g)
    (α : Fin (6 * g) → F) (hα : LinearIndependent K α) :
    let C := gabidulin K α (2 * g + 1)
    ∃ u₀ u₁ : Fin (6 * g) → F,
      uniformFraction (fun z : F => codeDistance K C (linePoint u₀ u₁ z) ≤ 2 * g) = 1 ∧
      codeDistance K C u₁ ≤ pairDistance K C u₀ u₁ ∧
      3 * g ≤ codeDistance K C u₁ := by sorry
end GabidulinProx.UniqueDecoding.Supplement
