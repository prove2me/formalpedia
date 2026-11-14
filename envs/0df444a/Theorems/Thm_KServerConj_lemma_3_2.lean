-- Prove2me | Theorems.Thm_KServerConj_lemma_3_2
-- name    : KServerConj.lemma_3_2
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T16:49:09.141779+00:00
-- url     : https://prove2.me/theorems/d163b60d-75b6-495a-92ca-da92f9a0ca9f
-- title:
--   Lemma 3.2 — rules for minor valuations (scaling, domination, block diagonal)
-- statement:
--   Let $\mu$ be the minimum maximal-minor valuation over a Hahn-series field $F((z^{\mathbb R}))$. For matrices $G$ with a finite set $R$ of rows:
--
--   1. if $A$ is an $R\times R$ matrix with $\det A\ne0$, then $\mu(AG)=\nu(\det A)+\mu(G)$;
--   2. if every column of a matrix $F$ (rows $R$) is a linear combination $\sum_j\lambda_jg_j$ of the columns of $G$ with coefficients of valuation $\nu(\lambda_j)\ge0$, then $\mu(F)\ge\mu(G)$;
--   3. if $G$ is block diagonal with (rectangular) blocks $G_1,\dots,G_s$, then
--
--   $$\mu(G)=\sum_{j=1}^s\mu(G_j).$$
--
--   These three rules are the whole toolkit of §4: they show the potential is invariant under normalization, and they compare the potentials before and after a request.
--
--   Differences from the source:
--   - generalization: spanning column families → all column families, with µ = ⊤ when every maximal minor vanishes; reason: with this convention the three rules hold without the spanning assumption; on spanning families they are the source's
--   - generalization: matrices over K → matrices over HahnSeries ℝ F for any field F; reason: the source's K is the case F = the field of rational functions
--   - encoding: µ(G) = min over increasing column choices, for spanning families → minorVal G : WithTop ℝ, the minimum over injections R ↪ ι, ⊤ when all maximal minors vanish; reason: column order only changes the sign of a determinant; on spanning families the two agree
--   - encoding: A invertible → det A ≠ 0; reason: over a field the two are equivalent
--   - encoding: G block diagonal with blocks G₁, …, G_s → Matrix.blockDiagonal' of a finite family of rectangular blocks; reason: same matrices up to the order of rows and columns, which changes no minor valuation
-- source:
--   Coester, Koutsoupias, Zbysiński, The k-server conjecture is true, arXiv:2609.15979 (version of 2026-11-03, sha256 7ca0380a…), Lemma 3.2, p.9 (pdf p.10)

import Mathlib
import Definitions.Def_KServerConj_minorVal

namespace KServerConj

/-- **Lemma 3.2 (Rules for minor valuations).** Coester, Koutsoupias, Zbysiński, *The k-server
conjecture is true*, arXiv:2609.15979 (version of 2026-11-03, sha256 7ca0380a…), printed p.9
(PDF p.10): "The following facts hold for spanning column families.
1. If A is an invertible d × d matrix, then µ(AG) = ν(det A) + µ(G).
2. If every column of a spanning family F is a linear combination of columns of G with coefficients
of nonnegative valuation, then µ(F) ≥ µ(G).
3. If G is block diagonal with blocks G₁, …, G_s, then µ(G) = ∑_{j=1}^s µ(G_j)."

**Formalization Note.** `µ` is `minorVal`, over Hahn series `HahnSeries ℝ F` with any coefficient
field `F` (the paper's `K` is the case `F = KServerConj.F k M`). The rows of `G` are a finite type
`R` (the paper's `d` coordinates) and its columns a finite type `ι`; the family in part 2 has
columns indexed by `κ`. Blocks in part 3 are rectangular, `G_j : Matrix (Rb j) (ιb j)`, assembled
by `Matrix.blockDiagonal'`. "Spanning" is not assumed: with `µ = ⊤` for a family whose maximal
minors all vanish, all three rules hold for every family. -/
theorem lemma_3_2 {F : Type*} [Field F] {R ι κ : Type*} [Fintype R] [DecidableEq R] [Fintype ι]
    [Fintype κ] {β : Type*} [Fintype β] [DecidableEq β] {Rb ιb : β → Type*}
    [∀ j, Fintype (Rb j)] [∀ j, Fintype (ιb j)] :
    (∀ (A : Matrix R R (HahnSeries ℝ F)) (G : Matrix R ι (HahnSeries ℝ F)), A.det ≠ 0 →
      minorVal (A * G) = HahnSeries.addVal ℝ F A.det + minorVal G) ∧
    (∀ (Fm : Matrix R κ (HahnSeries ℝ F)) (G : Matrix R ι (HahnSeries ℝ F)),
      (∀ c : κ, ∃ coeffs : ι → HahnSeries ℝ F, (∀ j, 0 ≤ HahnSeries.addVal ℝ F (coeffs j)) ∧
        ∀ i, Fm i c = ∑ j, coeffs j * G i j) →
      minorVal G ≤ minorVal Fm) ∧
    (∀ Gs : ∀ j : β, Matrix (Rb j) (ιb j) (HahnSeries ℝ F),
      minorVal (Matrix.blockDiagonal' Gs) = ∑ j, minorVal (Gs j)) := by sorry

end KServerConj
