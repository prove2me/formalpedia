-- Prove2me | Theorems.Thm_GabidulinProx_UniqueDecoding_Supplement_theorem_3_2
-- name    : GabidulinProx.UniqueDecoding.Supplement.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:45:38.697322+00:00
-- url     : https://prove2.me/theorems/e74c6e62-82f3-471f-83fe-cab5778f933a
-- title:
--   Theorem 3.2 — correlated agreement for general linear rank-metric codes
-- statement:
--   Let $L/K$ be an extension of finite fields with $q=|K|$, $q^m=|L|$ and $n\le m$, let $C\le L^n$ be an arbitrary $L$-linear code with minimum rank distance $d$, and let $e$ satisfy $1\le e\le\lfloor(d-1)/3\rfloor$ and $q^{e+1}<q^m$ (the setting of Lemma 3.1). For $u_0,u_1\in L^n$, if
--
--   $$\Pr_{z\in L}\bigl[d(u_0+zu_1,C)\le e\bigr]>\frac{q^{e+1}}{q^m},$$
--
--   then
--
--   $$d\bigl([u_0,u_1],C^2\bigr)\le e,$$
--
--   where the distance of the stacked pair is the joint column rank of $[u_0-c_0;u_1-c_1]$, minimized over $c_0,c_1\in C$. Theorem 1.2 is its relative-distance form.
--
--   Differences from the source:
--   - encoding: finite fields $\mathbb F_q\subseteq\mathbb F_{q^m}$ → finite fields $K,L$ with an algebra structure, $q=|K|$, $q^m=|L|$; reason: every finite extension of $\mathbb F_q$ has this form, and $|L|=|K|^{[L:K]}$
--   - encoding: rank after expanding each entry in a fixed $\mathbb F_q$-basis of $\mathbb F_{q^m}$ → $K$-dimension of the $K$-span of the columns (published `wordRank`, `codeDistance`, `pairDistance`); reason: the matrix rank does not depend on the chosen basis; the pair distance is the joint column rank of the $2m\times n$ matrix
--   - encoding: points $u_0+\lambda u_1$ with $\lambda$ uniform in $\mathbb F_{q^m}$ → parameters $z\in L$ with the published `linePoint` and `uniformFraction` (uniform over all of $L$, including $z=0$); reason: the line is the image of this parameterization and the probability is the counting measure normalized by $|L|$
--   - encoding: an $\mathbb F_{q^m}$-linear rank-metric code with minimum rank distance $d$ → an arbitrary submodule $C\le L^n$ and $d=$ `minRankDistance K C`, the least rank of a nonzero codeword ($0$ for $C=0$); reason: the source presupposes that $d$ exists; for $C=0$ the value $0$ makes the hypotheses on $d$ unsatisfiable, so no instance changes
--   - encoding: the standing assumption $n\le m$ of §1.1, p. 4, stated once for the whole paper → the explicit hypothesis $n\le[L:K]$; reason: it is a hypothesis of every result of the paper
-- source:
--   Songsong Li, Chaoping Xing, Chen Yuan, Ruiqi Zhu, Proximity Gaps for Gabidulin Codes and Applications, STOC 2027 submission #434 (October 2026), Theorem 3.2 p.17; setting of Lemma 3.1 p.16; standing assumption n ≤ m §1.1 p.4. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/434.pdf, SHA-256 8f644bcdfbdcd3478384d77d75a0f88ea116c29b14c52714f58bffb9ffda25cf

import Definitions.Def_GabidulinProx_UniqueDecoding_Supplement_Objects

namespace GabidulinProx.UniqueDecoding.Supplement

open GabidulinProx.UniqueDecoding

/-- Theorem 3.2, p.17 (correlated agreement): in the setting of Lemma 3.1 (an arbitrary
`L`-linear code of minimum rank distance `d`, `1 ≤ e ≤ ⌊(d-1)/3⌋`, `q^(e+1) < q^m`), if
`Pr_z[d(u₀ + z u₁, C) ≤ e] > q^(e+1)/q^m` then `d([u₀,u₁], C²) ≤ e`.
Standing assumption `n ≤ m` (§1.1, p.4). -/
theorem theorem_3_2 {K L : Type*} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
    {n : ℕ} (hnm : n ≤ Module.finrank K L) (C : Submodule L (Fin n → L)) {e : ℕ}
    (he : 1 ≤ e) (hed : e ≤ (minRankDistance K C - 1) / 3)
    (hqm : Fintype.card K ^ (e + 1) < Fintype.card L) (u₀ u₁ : Fin n → L)
    (hprob : uniformFraction (fun z : L => codeDistance K C (linePoint u₀ u₁ z) ≤ e) >
      ((Fintype.card K ^ (e + 1) : ℕ) : ℝ) / (Fintype.card L : ℝ)) :
    pairDistance K C u₀ u₁ ≤ e := by sorry
end GabidulinProx.UniqueDecoding.Supplement
