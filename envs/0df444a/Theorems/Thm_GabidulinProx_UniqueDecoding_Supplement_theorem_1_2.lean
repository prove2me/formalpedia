-- Prove2me | Theorems.Thm_GabidulinProx_UniqueDecoding_Supplement_theorem_1_2
-- name    : GabidulinProx.UniqueDecoding.Supplement.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:41:49.243675+00:00
-- url     : https://prove2.me/theorems/ed595298-e506-453a-8ba4-64ecfb1c1ebe
-- title:
--   Theorem 1.2 — a $(d-1)/(3n)$ proximity gap for every linear rank-metric code
-- statement:
--   Let $L/K$ be an extension of finite fields with $q=|K|$, $q^m=|L|$ and $n\le m$, and let $C\le L^n$ be an arbitrary $L$-linear rank-metric code with minimum rank distance $d$. Write $\Delta(x,C)=d(x,C)/n$ for the relative rank distance. Let $\delta$ be a real number with
--
--   $$0<\delta\le\frac{d-1}{3n},\qquad e=\lfloor\delta n\rfloor .$$
--
--   Then:
--
--   1. $C$ has a $(\delta,q^{e+1}/q^m)$-proximity gap for lines (Definition 1.1): for all $u_0,u_1\in L^n$, if $\Pr_{\lambda\in L}[\Delta(u_0+\lambda u_1,C)\le\delta]>q^{e+1}/q^m$, then $\Delta([u_0,u_1],C^2)\le\delta$, where the distance of the stacked pair is the joint column rank of $[u_0-c_0;u_1-c_1]$ minimized over $c_0,c_1\in C$.
--   2. Consequently, for all $u_0,u_1$, either every point $u_0+\lambda u_1$ is $\delta$-close to $C$, or $\Pr_{\lambda\in L}[\Delta(u_0+\lambda u_1,C)\le\delta]\le q^{e+1}/q^m$.
--
--   The radius $e=0$ (that is, $\delta<1/n$) is included, and no hypothesis $q^{e+1}<q^m$ is made. Theorem 1.2 is the relative-distance form of the correlated agreement Theorem 3.2 for general codes.
--
--   Differences from the source:
--   - encoding: finite fields $\mathbb F_q\subseteq\mathbb F_{q^m}$ → finite fields $K,L$ with an algebra structure, $q=|K|$, $q^m=|L|$; reason: every finite extension of $\mathbb F_q$ has this form, and $|L|=|K|^{[L:K]}$
--   - encoding: rank after expanding each entry in a fixed $\mathbb F_q$-basis of $\mathbb F_{q^m}$ → $K$-dimension of the $K$-span of the columns (published `wordRank`, `codeDistance`, `pairDistance`); reason: the matrix rank does not depend on the chosen basis; the pair distance is the joint column rank of the $2m\times n$ matrix
--   - encoding: points $u_0+\lambda u_1$ with $\lambda$ uniform in $\mathbb F_{q^m}$ → parameters $z\in L$ with the published `linePoint` and `uniformFraction` (uniform over all of $L$, including $z=0$); reason: the line is the image of this parameterization and the probability is the counting measure normalized by $|L|$
--   - encoding: an $\mathbb F_{q^m}$-linear rank-metric code with minimum rank distance $d$ → an arbitrary submodule $C\le L^n$ and $d=$ `minRankDistance K C`, the least rank of a nonzero codeword ($0$ for $C=0$); reason: the source presupposes that $d$ exists; for $C=0$ the value $0$ makes the hypotheses on $d$ unsatisfiable, so no instance changes
--   - encoding: the standing assumption $n\le m$ of §1.1, p. 4, stated once for the whole paper → the explicit hypothesis $n\le[L:K]$; reason: it is a hypothesis of every result of the paper
--   - encoding: the bound $(d-1)/3n$ → $((d:\mathbb R)-1)/(3n)$ in real arithmetic, with $e=\lfloor\delta n\rfloor_+$; reason: real subtraction avoids natural truncation; at $n=0$ the bound is $0$ and the hypothesis $0<\delta$ excludes the case, which the source never considers
-- source:
--   Songsong Li, Chaoping Xing, Chen Yuan, Ruiqi Zhu, Proximity Gaps for Gabidulin Codes and Applications, STOC 2027 submission #434 (October 2026), Theorem 1.2 p.5; Definition 1.1 p.4; standing assumption n ≤ m §1.1 p.4. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/434.pdf, SHA-256 8f644bcdfbdcd3478384d77d75a0f88ea116c29b14c52714f58bffb9ffda25cf

import Definitions.Def_GabidulinProx_UniqueDecoding_Supplement_Objects

namespace GabidulinProx.UniqueDecoding.Supplement

open GabidulinProx.UniqueDecoding

/-- Theorem 1.2, p.5: every `L`-linear rank-metric code with minimum rank distance `d`
has a `(δ, q^(e+1)/q^m)`-proximity gap for every real `0 < δ ≤ (d-1)/(3n)`, `e = ⌊δn⌋`
(including `e = 0`); consequently every line is entirely `δ`-close or has at most a
`q^(e+1)/q^m` fraction of `δ`-close points. Standing assumption `n ≤ m` (§1.1, p.4). -/
theorem theorem_1_2 {K L : Type*} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
    {n : ℕ} (hnm : n ≤ Module.finrank K L) (C : Submodule L (Fin n → L))
    (δ : ℝ) (hδ : 0 < δ) (hδmax : δ ≤ ((minRankDistance K C : ℝ) - 1) / (3 * (n : ℝ))) :
    let e := ⌊δ * (n : ℝ)⌋₊
    HasProximityGap K C δ (((Fintype.card K ^ (e + 1) : ℕ) : ℝ) / (Fintype.card L : ℝ)) ∧
      ∀ u₀ u₁ : Fin n → L,
        (∀ z : L, (codeDistance K C (linePoint u₀ u₁ z) : ℝ) / (n : ℝ) ≤ δ) ∨
          uniformFraction (fun z : L => (codeDistance K C (linePoint u₀ u₁ z) : ℝ) / (n : ℝ) ≤ δ) ≤
            ((Fintype.card K ^ (e + 1) : ℕ) : ℝ) / (Fintype.card L : ℝ) := by sorry
end GabidulinProx.UniqueDecoding.Supplement
