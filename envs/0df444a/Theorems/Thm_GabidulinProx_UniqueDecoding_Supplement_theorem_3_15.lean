-- Prove2me | Theorems.Thm_GabidulinProx_UniqueDecoding_Supplement_theorem_3_15
-- name    : GabidulinProx.UniqueDecoding.Supplement.theorem_3_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:46:55.728585+00:00
-- url     : https://prove2.me/theorems/ff102058-bc14-4f70-83b8-48eb035f42cb
-- title:
--   Theorem 3.15 — explicit code and line for the lower bound at $e=(d-1)/2$
-- statement:
--   Fix integers $r\ge1$ and $2\le c\le h$ and put $e=r$, $n=c(r+1)$, $m=h(r+1)$, $k=n-2r$, $Q=q^{r+1}$. Let $\mathbb F_q\subseteq\mathbb F_Q\subseteq E=\mathbb F_{q^m}=\mathbb F_{Q^h}$, let $V\subseteq E$ be any $c$-dimensional $\mathbb F_Q$-subspace, let $A=(\alpha_1,\dots,\alpha_n)$ be any $\mathbb F_q$-basis of $V$, and let $C=G(A,k)\subseteq E^n$. Let $H\subseteq E$ be the set of Lemma 3.14. Then:
--
--   1. the minimum rank distance of $C$ is $d=2r+1$ (so $e=r=(d-1)/2$);
--   2. with $u_0=(\alpha_i^{\,q^{n-e}})_i$, $u_1=(\alpha_i^{\,q^{n-e-1}})_i$ and $\ell(\lambda)=u_0+\lambda u_1$, every $\lambda\in H$ satisfies $d(\ell(\lambda),C)\le e$;
--   3. $d([u_0,u_1],C^2)\ge e+1$.
--
--   The powers are ordinary powers $x^{q^j}$, i.e. the evaluations of the monomials $X^{q^{n-e}}$ and $X^{q^{n-e-1}}$ on $A$. With Lemma 3.14 this gives Theorem 1.5.
--
--   Differences from the source:
--   - encoding: finite fields $\mathbb F_q\subseteq\mathbb F_{q^m}$ → finite fields $K,L$ with an algebra structure, $q=|K|$, $q^m=|L|$; reason: every finite extension of $\mathbb F_q$ has this form, and $|L|=|K|^{[L:K]}$
--   - encoding: rank after expanding each entry in a fixed $\mathbb F_q$-basis of $\mathbb F_{q^m}$ → $K$-dimension of the $K$-span of the columns (published `wordRank`, `codeDistance`, `pairDistance`); reason: the matrix rank does not depend on the chosen basis; the pair distance is the joint column rank of the $2m\times n$ matrix
--   - encoding: points $u_0+\lambda u_1$ with $\lambda$ uniform in $\mathbb F_{q^m}$ → parameters $z\in L$ with the published `linePoint` and `uniformFraction` (uniform over all of $L$, including $z=0$); reason: the line is the image of this parameterization and the probability is the counting measure normalized by $|L|$
--   - encoding: the subfield $\mathbb F_Q$, $Q=q^{r+1}$, of $E=\mathbb F_{Q^h}$ → an intermediate finite field `KQ` with `IsScalarTower K KQ E`, $|KQ|=q^{r+1}$ and $[E:KQ]=h$; reason: a finite field has exactly one subfield of each admissible size; $m=h(r+1)$ follows
--   - encoding: $A$ an $\mathbb F_q$-basis of $V$ → $\alpha$ $K$-linearly independent with $K$-span equal to $V$ as a set; reason: this is the definition of a basis of the $K$-subspace underlying $V$
-- source:
--   Songsong Li, Chaoping Xing, Chen Yuan, Ruiqi Zhu, Proximity Gaps for Gabidulin Codes and Applications, STOC 2027 submission #434 (October 2026), §3.4 setting p.28 and Theorem 3.15 p.28; proof pp.28–29. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/434.pdf, SHA-256 8f644bcdfbdcd3478384d77d75a0f88ea116c29b14c52714f58bffb9ffda25cf

import Definitions.Def_GabidulinProx_UniqueDecoding_Supplement_Objects

namespace GabidulinProx.UniqueDecoding.Supplement

open GabidulinProx.UniqueDecoding

/-- Theorem 3.15, p.28: in the setting of Lemma 3.14 (`K ⊆ KQ ⊆ E`, `|KQ| = q^(r+1)`,
`[E : KQ] = h`, `r ≥ 1`, `2 ≤ c ≤ h`, `n = c(r+1)`, `k = n - 2r`, `e = r`), for every
`c`-dimensional `KQ`-subspace `V ⊆ E` and every `K`-basis `A = (α_i)` of `V`, the code
`C = G(A, k)` has minimum distance `2r+1`; with `u₀ = (α_i^(q^(n-e)))_i`,
`u₁ = (α_i^(q^(n-e-1)))_i`, `d(u₀ + λu₁, C) ≤ e` for every `λ ∈ H`, and
`d([u₀,u₁], C²) ≥ e+1`. -/
theorem theorem_3_15 {K KQ E : Type*} [Field K] [Fintype K] [Field KQ] [Fintype KQ]
    [Field E] [Fintype E] [Algebra K KQ] [Algebra KQ E] [Algebra K E] [IsScalarTower K KQ E]
    (r c h : ℕ) (hr : 1 ≤ r) (hc : 2 ≤ c) (hch : c ≤ h)
    (hQ : Fintype.card KQ = Fintype.card K ^ (r + 1)) (hE : Module.finrank KQ E = h)
    (V : Submodule KQ E) (hV : Module.finrank KQ V = c)
    (α : Fin (c * (r + 1)) → E) (hα : LinearIndependent K α)
    (hspan : (Submodule.span K (Set.range α) : Set E) = (V : Set E)) :
    let n := c * (r + 1)
    let C := gabidulin K α (n - 2 * r)
    let u₀ : Fin n → E := fun i => α i ^ (Fintype.card K ^ (n - r))
    let u₁ : Fin n → E := fun i => α i ^ (Fintype.card K ^ (n - r - 1))
    minRankDistance K C = 2 * r + 1 ∧
      (∀ z ∈ paramSet K KQ V, codeDistance K C (linePoint u₀ u₁ z) ≤ r) ∧
      r + 1 ≤ pairDistance K C u₀ u₁ := by sorry
end GabidulinProx.UniqueDecoding.Supplement
