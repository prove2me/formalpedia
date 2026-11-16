-- Prove2me | Theorems.Thm_GabidulinProx_UniqueDecoding_Supplement_theorem_3_13
-- name    : GabidulinProx.UniqueDecoding.Supplement.theorem_3_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:46:30.830845+00:00
-- url     : https://prove2.me/theorems/35048967-d784-4926-85d1-61be39f322c3
-- title:
--   Theorem 3.13 — the counterexample family for every $N\ge6$
-- statement:
--   Fix an integer $N\ge6$. Let $K=\mathbb F_q$ be any finite field and $g\ge1$; put $Q=q^g$, $F=\mathbb F_{Q^N}=\mathbb F_{q^{Ng}}$ and $n=Ng$. Let $A$ be any $\mathbb F_q$-basis of $F$ and $C=G(A,(N-4)g+1)\subseteq F^n$, whose distance is $d=n-k+1=4g$. Then there exist words $u_0,u_1\in F^n$ such that
--
--   $$\Pr_{\lambda\in F}\bigl[d(u_0+\lambda u_1,C)\le d/2\bigr]\ge1-Q^{-N}=1-q^{-Ng}$$
--
--   and
--
--   $$d([u_0,u_1],C^2)\ge3g=\tfrac{3d}4 ;$$
--
--   if $N$ is even, the probability above equals $1$ (for the same $u_0,u_1$). The family has rate approaching one as $N$ grows.
--
--   Differences from the source:
--   - encoding: finite fields $\mathbb F_q\subseteq\mathbb F_{q^m}$ → finite fields $K,L$ with an algebra structure, $q=|K|$, $q^m=|L|$; reason: every finite extension of $\mathbb F_q$ has this form, and $|L|=|K|^{[L:K]}$
--   - encoding: rank after expanding each entry in a fixed $\mathbb F_q$-basis of $\mathbb F_{q^m}$ → $K$-dimension of the $K$-span of the columns (published `wordRank`, `codeDistance`, `pairDistance`); reason: the matrix rank does not depend on the chosen basis; the pair distance is the joint column rank of the $2m\times n$ matrix
--   - encoding: points $u_0+\lambda u_1$ with $\lambda$ uniform in $\mathbb F_{q^m}$ → parameters $z\in L$ with the published `linePoint` and `uniformFraction` (uniform over all of $L$, including $z=0$); reason: the line is the image of this parameterization and the probability is the counting measure normalized by $|L|$
--   - encoding: any $\mathbb F_q$-basis $A=\{\alpha_1,\dots,\alpha_n\}$ of the field and $C=G(A,k)$ → every $K$-linearly independent family $\alpha:\mathrm{Fin}\,n\to L$ with $[L:K]=n$ and the published `gabidulin K α k`; reason: $n$ independent vectors in an $n$-dimensional space form a basis; the published code is the image of the $q$-linearized evaluation map
--   - encoding: $d/2$ with $d=4g$, and $1-Q^{-N}$ → the number $2g$, and $1-1/|F|$; reason: $d=Ng-((N-4)g+1)+1=4g$ and $|F|=q^{Ng}=Q^N$
-- source:
--   Songsong Li, Chaoping Xing, Chen Yuan, Ruiqi Zhu, Proximity Gaps for Gabidulin Codes and Applications, STOC 2027 submission #434 (October 2026), Theorem 3.13 p.27; extension of Lemmas 3.10–3.11 in the running text p.27. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/434.pdf, SHA-256 8f644bcdfbdcd3478384d77d75a0f88ea116c29b14c52714f58bffb9ffda25cf

import Definitions.Def_GabidulinProx_UniqueDecoding_Supplement_Objects

namespace GabidulinProx.UniqueDecoding.Supplement

open GabidulinProx.UniqueDecoding

/-- Theorem 3.13, p.27: fix `N ≥ 6`. For every finite field `K` and `g ≥ 1`, with
`Q = q^g`, `F = F_{Q^N}`, `n = Ng`, any `K`-basis `A` of `F` and `C = G(A, (N-4)g+1)` (so
`d = 4g`), there are `u₀, u₁` with `Pr_z[d(u₀ + z u₁, C) ≤ d/2] ≥ 1 - Q^(-N) = 1 - 1/|F|`
and `d([u₀,u₁], C²) ≥ 3g = 3d/4`; if `N` is even the probability equals `1`. -/
theorem theorem_3_13 (N : ℕ) (hN : 6 ≤ N) {K F : Type*} [Field K] [Fintype K] [Field F]
    [Fintype F] [Algebra K F] (g : ℕ) (hg : 1 ≤ g) (hdim : Module.finrank K F = N * g)
    (α : Fin (N * g) → F) (hα : LinearIndependent K α) :
    let C := gabidulin K α ((N - 4) * g + 1)
    ∃ u₀ u₁ : Fin (N * g) → F,
      uniformFraction (fun z : F => codeDistance K C (linePoint u₀ u₁ z) ≤ 2 * g) ≥
        1 - 1 / (Fintype.card F : ℝ) ∧
      3 * g ≤ pairDistance K C u₀ u₁ ∧
      (Even N →
        uniformFraction (fun z : F => codeDistance K C (linePoint u₀ u₁ z) ≤ 2 * g) = 1) := by sorry
end GabidulinProx.UniqueDecoding.Supplement
