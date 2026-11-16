-- Prove2me | Theorems.Thm_GabidulinProx_UniqueDecoding_Supplement_theorem_1_4
-- name    : GabidulinProx.UniqueDecoding.Supplement.theorem_1_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:44:08.90961+00:00
-- url     : https://prove2.me/theorems/1d20c9d8-8a18-4aa5-90d0-221af95dac42
-- title:
--   Theorem 1.4 — counterexample for Gabidulin codes at proximity $d/(2n)$
-- statement:
--   Let $K=\mathbb F_q$ be any finite field and $g\ge1$. Put $n=6g$ and let $L=\mathbb F_{q^n}$. For every $\mathbb F_q$-basis $A=(\alpha_1,\dots,\alpha_n)$ of $L$, let $C=G(A,2g+1)\subseteq L^n$ be the Gabidulin code. Then:
--
--   1. $C$ is an $[n,2g+1,4g]$ code: $\dim_L C=2g+1$ and its minimum rank distance is $d=4g$;
--   2. there exist $u_0,u_1\in L^n$ such that
--
--   $$\Pr_{\lambda\in L}\bigl[d(u_0+\lambda u_1,C)\le d/2\bigr]=1,$$
--
--   but
--
--   $$d([u_0,u_1],C^2)\ge d(u_1,C)\ge\tfrac{3d}{4}>\tfrac d2 .$$
--
--   Here $d/2=2g$ and $3d/4=3g$. The theorem shows that the radius $(d-1)/(2n)$ of Theorem 1.3 cannot be raised to $d/(2n)$.
--
--   Differences from the source:
--   - encoding: finite fields $\mathbb F_q\subseteq\mathbb F_{q^m}$ → finite fields $K,L$ with an algebra structure, $q=|K|$, $q^m=|L|$; reason: every finite extension of $\mathbb F_q$ has this form, and $|L|=|K|^{[L:K]}$
--   - encoding: rank after expanding each entry in a fixed $\mathbb F_q$-basis of $\mathbb F_{q^m}$ → $K$-dimension of the $K$-span of the columns (published `wordRank`, `codeDistance`, `pairDistance`); reason: the matrix rank does not depend on the chosen basis; the pair distance is the joint column rank of the $2m\times n$ matrix
--   - encoding: points $u_0+\lambda u_1$ with $\lambda$ uniform in $\mathbb F_{q^m}$ → parameters $z\in L$ with the published `linePoint` and `uniformFraction` (uniform over all of $L$, including $z=0$); reason: the line is the image of this parameterization and the probability is the counting measure normalized by $|L|$
--   - encoding: any $\mathbb F_q$-basis $A=\{\alpha_1,\dots,\alpha_n\}$ of the field and $C=G(A,k)$ → every $K$-linearly independent family $\alpha:\mathrm{Fin}\,n\to L$ with $[L:K]=n$ and the published `gabidulin K α k`; reason: $n$ independent vectors in an $n$-dimensional space form a basis; the published code is the image of the $q$-linearized evaluation map
--   - generalization: "let $C$ be an $[n,2g+1,4g]$ Gabidulin code", the parameters given with the code → the parameters $\dim_L C=2g+1$ and minimum rank distance $4g$ are conclusions, for every Gabidulin code $G(A,2g+1)$ with $A$ a basis; reason: every such code has these parameters, so the Lean statement specializes to the source's claim and adds them as proved facts
--   - encoding: $d/2$ and $3d/4$ with $d=4g$ → the numbers $2g$ and $3g$; reason: $d=4g$ is a conclusion of the same statement
-- source:
--   Songsong Li, Chaoping Xing, Chen Yuan, Ruiqi Zhu, Proximity Gaps for Gabidulin Codes and Applications, STOC 2027 submission #434 (October 2026), Theorem 1.4 p.5; body Theorem 3.12 p.26. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/434.pdf, SHA-256 8f644bcdfbdcd3478384d77d75a0f88ea116c29b14c52714f58bffb9ffda25cf

import Definitions.Def_GabidulinProx_UniqueDecoding_Supplement_Objects

namespace GabidulinProx.UniqueDecoding.Supplement

open GabidulinProx.UniqueDecoding

/-- Theorem 1.4, p.5: for every finite field `K` (`q = |K|`) and `g ≥ 1`, with `n = 6g` and
`L = F_{q^n}`, every Gabidulin code `C = G(A, 2g+1)` (`A` a `K`-basis of `L`) is an
`[n, 2g+1, 4g]` code, and there are `u₀, u₁` with `Pr_z[d(u₀ + z u₁, C) ≤ d/2] = 1` but
`d([u₀,u₁], C²) ≥ d(u₁, C) ≥ 3d/4 > d/2`; here `d/2 = 2g`, `3d/4 = 3g`. -/
theorem theorem_1_4 {K L : Type*} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
    (g : ℕ) (hg : 1 ≤ g) (hdim : Module.finrank K L = 6 * g)
    (α : Fin (6 * g) → L) (hα : LinearIndependent K α) :
    let C := gabidulin K α (2 * g + 1)
    Module.finrank L C = 2 * g + 1 ∧ minRankDistance K C = 4 * g ∧
      ∃ u₀ u₁ : Fin (6 * g) → L,
        uniformFraction (fun z : L => codeDistance K C (linePoint u₀ u₁ z) ≤ 2 * g) = 1 ∧
        codeDistance K C u₁ ≤ pairDistance K C u₀ u₁ ∧
        3 * g ≤ codeDistance K C u₁ ∧ 2 * g < 3 * g := by sorry
end GabidulinProx.UniqueDecoding.Supplement
