-- Prove2me | Theorems.Thm_GL2QFT_table_2_completeness
-- name    : GL2QFT.table_2_completeness
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:19:01.256801+00:00
-- url     : https://prove2.me/theorems/82ed535a-3e54-41f4-9d5c-737a30e01358
-- title:
--   Table 2 — the listed representations are all the irreducible representations of $\mathrm{GL}_2(\mathbb F_q)$
-- statement:
--   Let $R_\mu$, for $\mu$ in the label set of Table 2, be the representations of §6.1.1 in the Gelfand–Tsetlin bases of §6.2. Then:
--   1. every $R_\mu$ is a unitary representation of $G=\mathrm{GL}_2(\mathbb F_q)$;
--   2. every $R_\mu$ is irreducible;
--   3. $R_\mu\not\cong R_{\mu'}$ for $\mu\neq\mu'$;
--   4. there are $(q-1)(q-2)/2$ principal-series labels and $q(q-1)/2$ cuspidal labels;
--   5. the dimensions satisfy
--   $$(q-1)\cdot1^2+(q-1)\cdot q^2+\frac{(q-1)(q-2)}{2}(q+1)^2+\frac{q(q-1)}{2}(q-1)^2=(q^2-1)(q^2-q)=|G|;$$
--   6. every irreducible representation of $G$ is equivalent to some $R_\mu$.
--
--   This makes the family a complete set of representatives of $\widehat G$, so the transform $\mathfrak F_G$ of (22) built from it is a Fourier transform in the sense of Definition 2.6.
--
--   **Formalization Note** The homomorphism property of $\pi_\theta$ in the model (99)–(100) is Piatetski-Shapiro's construction ([Pia83, §13], cited p.36).
--
--   Differences from the source:
--   - reading: "tells us that these are all the irreducible representations of $G$" → clauses 1–6; reason: the dimension count proves completeness only for a family of pairwise inequivalent irreducible representations, which Table 2 asserts ("Irreducible representations of $\mathrm{GL}_2(\mathbb F_q)$"); all of these are stated
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols, Quantum Fourier transform toolbox, arXiv:2608.28573 (held version, sha256 ecd45073…), §6.1.1, Table 2 and the following sentence, p.36 (PDF p.37)

import Definitions.Def_GL2QFT_Irreps

open Classical

namespace GL2QFT

open FieldData

/-- arXiv:2608.28573 (held version, sha256 ecd45073…), **§6.1.1, Table 2 and the sentence after it**,
p.36 (PDF p.37): "The sum of their squared dimensions
`(q − 1) · 1² + (q − 1) · q² + ((q − 1)(q − 2)/2) · (q + 1)² + (q(q − 1)/2) · (q − 1)² = (q² − 1)(q² − q) = |G|`
tells us that these are all the irreducible representations of `G`."

For the family `R_μ`, `μ ∈ Irr D` (Table 2, in the Gelfand–Tsetlin bases of §6.2):
1. every `R_μ` is a unitary representation of `GL₂(F_q)` (for `π_θ` this is [Pia83, §13], cited
   p.36);
2. every `R_μ` is irreducible;
3. `R_μ ≇ R_{μ'}` for `μ ≠ μ'`;
4. the Table 2 counts: `(q−1)(q−2)/2` principal-series labels `α ≺ β` and `q(q−1)/2` cuspidal
   labels (there are `q − 1` determinant and `q − 1` Steinberg labels by definition);
5. `Σ_μ d_μ² = |G| = (q² − 1)(q² − q)`;
6. these are all the irreducible representations: every irreducible representation of
   `GL₂(F_q)` is equivalent to some `R_μ`. -/
theorem table_2_completeness (D : FieldData) :
    (∀ μ : D.Irr, IsUnitaryRep (D.R μ)) ∧
    (∀ μ : D.Irr, IsIrreducibleRep (D.R μ)) ∧
    (∀ μ μ' : D.Irr, μ ≠ μ' → ¬ RepEquiv (D.R μ) (D.R μ')) ∧
    (Fintype.card {ab : D.Lab × D.Lab // ab.1.val < ab.2.val} = (D.q - 1) * (D.q - 2) / 2 ∧
      Fintype.card {k : D.Lab2 // D.IsCuspLabel k} = D.q * (D.q - 1) / 2) ∧
    (∑ μ : D.Irr, Fintype.card (D.Bas μ) ^ 2 = Fintype.card D.G ∧
      Fintype.card D.G = (D.q ^ 2 - 1) * (D.q ^ 2 - D.q)) ∧
    (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ρ : D.G → Matrix ι ι ℂ),
      IsMatRep ρ → IsIrreducibleRep ρ → ∃ μ : D.Irr, RepEquiv (D.R μ) ρ) := by sorry

end GL2QFT
