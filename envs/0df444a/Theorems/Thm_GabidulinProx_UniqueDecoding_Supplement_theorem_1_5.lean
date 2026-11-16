-- Prove2me | Theorems.Thm_GabidulinProx_UniqueDecoding_Supplement_theorem_1_5
-- name    : GabidulinProx.UniqueDecoding.Supplement.theorem_1_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:45:17.534505+00:00
-- url     : https://prove2.me/theorems/b9d36b5c-8b27-4b4f-b438-b9bfe0c20505
-- title:
--   Theorem 1.5 — a tight lower bound on $\varepsilon$ at proximity $(d-1)/(2n)$
-- statement:
--   Let $K=\mathbb F_q$ be any finite field and let $r\ge1$, $2\le c\le h$ be integers. Put $n=c(r+1)$, $m=h(r+1)$, $e=r$, and let $L=\mathbb F_{q^m}$. Then there exist an $[n,n-2r,2r+1]$ Gabidulin code $C=G(A,n-2r)\subseteq L^n$ (with $A$ $\mathbb F_q$-linearly independent, $\dim_LC=n-2r$, minimum rank distance $2r+1$) and vectors $u_0,u_1\in L^n$ such that
--
--   $$\Pr_{\lambda\in L}\bigl[d(u_0+\lambda u_1,C)\le e\bigr]\ge\frac{q^n-1}{(q-1)q^m}$$
--
--   but
--
--   $$d([u_0,u_1],C^2)\ge d(u_1,C)\ge e+1 .$$
--
--   Moreover the bound is $\Theta(q^{n-1}/q^m)$, with explicit constants:
--
--   $$\frac{q^{n-1}}{q^m}\le\frac{q^n-1}{(q-1)q^m}\le\frac{2q^{n-1}}{q^m}.$$
--
--   Hence the $q^{n-1}/q^m$ dependence of the soundness error in Theorem 1.3 is tight up to a constant factor.
--
--   Differences from the source:
--   - encoding: finite fields $\mathbb F_q\subseteq\mathbb F_{q^m}$ → finite fields $K,L$ with an algebra structure, $q=|K|$, $q^m=|L|$; reason: every finite extension of $\mathbb F_q$ has this form, and $|L|=|K|^{[L:K]}$
--   - encoding: rank after expanding each entry in a fixed $\mathbb F_q$-basis of $\mathbb F_{q^m}$ → $K$-dimension of the $K$-span of the columns (published `wordRank`, `codeDistance`, `pairDistance`); reason: the matrix rank does not depend on the chosen basis; the pair distance is the joint column rank of the $2m\times n$ matrix
--   - encoding: points $u_0+\lambda u_1$ with $\lambda$ uniform in $\mathbb F_{q^m}$ → parameters $z\in L$ with the published `linePoint` and `uniformFraction` (uniform over all of $L$, including $z=0$); reason: the line is the image of this parameterization and the probability is the counting measure normalized by $|L|$
--   - encoding: an $[n,n-2r,2r+1]$ Gabidulin code $C=G(A,n-2r)\subseteq\mathbb F_{q^m}^n$ → $\exists\,\alpha$ $K$-linearly independent with $\dim_L$ `gabidulin K α (n-2r)` $=n-2r$ and `minRankDistance` $=2r+1$; reason: all three parameters are stated as conclusions about the exhibited code
--   - reading: $\frac{q^n-1}{(q-1)q^m}=\Theta\bigl(\frac{q^{n-1}}{q^m}\bigr)$ → the two explicit inequalities with constants $1$ and $2$, in addition to the exact bound; reason: the asymptotic notation has no stated constants; $1$ and $2$ are the constants valid for every $q\ge2$, and the exact fraction is kept
-- source:
--   Songsong Li, Chaoping Xing, Chen Yuan, Ruiqi Zhu, Proximity Gaps for Gabidulin Codes and Applications, STOC 2027 submission #434 (October 2026), Theorem 1.5 p.6; body Theorem 3.15 p.28 and Remark 3.16 p.29. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/434.pdf, SHA-256 8f644bcdfbdcd3478384d77d75a0f88ea116c29b14c52714f58bffb9ffda25cf

import Definitions.Def_GabidulinProx_UniqueDecoding_Supplement_Objects

namespace GabidulinProx.UniqueDecoding.Supplement

open GabidulinProx.UniqueDecoding

/-- Theorem 1.5, p.6: for every finite field `K` (`q = |K|`), `r ≥ 1`, `2 ≤ c ≤ h`, with
`n = c(r+1)`, `m = h(r+1)`, `e = r` and `L = F_{q^m}`, there are an `[n, n-2r, 2r+1]` Gabidulin
code `C ⊆ Lⁿ` and `u₀, u₁` with `Pr_z[d(u₀ + z u₁, C) ≤ e] ≥ (q^n-1)/((q-1)q^m)` but
`d([u₀,u₁], C²) ≥ d(u₁, C) ≥ e+1`; and `(q^n-1)/((q-1)q^m) = Θ(q^(n-1)/q^m)`, written with
the explicit constants `1` and `2`. -/
theorem theorem_1_5 {K L : Type*} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
    (r c h : ℕ) (hr : 1 ≤ r) (hc : 2 ≤ c) (hch : c ≤ h)
    (hdim : Module.finrank K L = h * (r + 1)) :
    let n := c * (r + 1)
    let q := Fintype.card K
    (∃ α : Fin n → L, LinearIndependent K α ∧
      Module.finrank L (gabidulin K α (n - 2 * r)) = n - 2 * r ∧
      minRankDistance K (gabidulin K α (n - 2 * r)) = 2 * r + 1 ∧
      ∃ u₀ u₁ : Fin n → L,
        uniformFraction (fun z : L =>
            codeDistance K (gabidulin K α (n - 2 * r)) (linePoint u₀ u₁ z) ≤ r) ≥
          ((q : ℝ) ^ n - 1) / (((q : ℝ) - 1) * (Fintype.card L : ℝ)) ∧
        codeDistance K (gabidulin K α (n - 2 * r)) u₁ ≤
          pairDistance K (gabidulin K α (n - 2 * r)) u₀ u₁ ∧
        r + 1 ≤ codeDistance K (gabidulin K α (n - 2 * r)) u₁) ∧
    (q : ℝ) ^ (n - 1) / (Fintype.card L : ℝ) ≤
        ((q : ℝ) ^ n - 1) / (((q : ℝ) - 1) * (Fintype.card L : ℝ)) ∧
      ((q : ℝ) ^ n - 1) / (((q : ℝ) - 1) * (Fintype.card L : ℝ)) ≤
        2 * (q : ℝ) ^ (n - 1) / (Fintype.card L : ℝ) := by sorry
end GabidulinProx.UniqueDecoding.Supplement
