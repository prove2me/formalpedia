-- Prove2me | Theorems.Thm_GoodQLTC_lemma_6_2
-- name    : GoodQLTC.lemma_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:49:19.09229+00:00
-- url     : https://prove2.me/theorems/2162249f-277b-4558-b0c4-acd462439b41
-- title:
--   Lemma 6.2: universal implies collective product expansion
-- statement:
--   Let $F=\mathbb F_{2^s}$, $\emptyset\ne I\subseteq[t]$, and $C_i\subseteq F^{\Omega_i}$ ($i\in I$) linear codes on finite sets. If $\{C_i\}_{i\in I}$ is universally $\rho$-product-expanding, then it has collective $\rho$-product expansion over every extension $E/F$: for every finite-dimensional $E$-space $R$, every $x\in A^E(\{C_i\};R)$ splits as $x=\sum_ix_i$ with $x_i\in A^E_i(C_i;R)$ and $\rho\sum_in_i\ell_i(x_i)\le|x|_b$.
--
--   It upgrades scalar product expansion to vector-valued coefficients, as needed for local filling.
--
--   Differences from the source:
--   - generalization: universal product expansion over every field extension E/F → the hypothesis quantifies over extensions E in one universe u (a parameter of the theorem); reason: Lean has no type of all fields; the paper's hypothesis (all extensions) implies the one-universe hypothesis, so the statement specializes to the source's
-- source:
--   Gay, Jeronimo, Asymptotically Good Quantum Locally Testable Codes, arXiv:2609.20780 (held version, sha256 04ad03ca…), Lemma 6.2, p.21 (PDF p.24)

import Mathlib
import Definitions.Def_GoodQLTC_IsProductExpanding
import Definitions.Def_GoodQLTC_HasCollectiveExpansion

namespace GoodQLTC

universe u v

/-- **Lemma 6.2** (universal implies collective), Gay–Jeronimo, arXiv:2609.20780 (held version),
p.21: let `∅ ≠ I ⊆ [t]`. A universally `ρ`-product-expanding family `{C_i}_{i∈I}` has collective
`ρ`-product expansion over every extension `E/F`.

**Formalization Note.** `F` is a field with `2^s` elements, `s ≥ 1` (§4.2); `Ω_i` are finite sets
and `C_i ⊆ F^{Ω_i}` linear codes. Extensions `E` range over a universe `u` (the same in the
hypothesis and the conclusion), and coefficient spaces `R` over a universe `v`. -/
theorem lemma_6_2 {F : Type} [Field F] [Fintype F] {s : ℕ} (hs : 1 ≤ s)
    (hF : Fintype.card F = 2 ^ s) {t : ℕ} (I : Finset (Fin t)) (hI : I.Nonempty)
    {Ω : I → Type} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]
    (C : ∀ i, Submodule F (Ω i → F)) (ρ : ℝ) (hC : IsUnivProductExpanding.{u} ρ C)
    (E : Type u) [Field E] [Algebra F E] :
    HasCollectiveExpansion.{u, v} E ρ C := by sorry

end GoodQLTC
