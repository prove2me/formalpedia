-- Prove2me | Theorems.Thm_GenCountSampleLLL_lemma_6_2
-- name    : GenCountSampleLLL.lemma_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:56:18.344568+00:00
-- url     : https://prove2.me/theorems/7ab2d045-e5ff-433f-a09e-afe69be4f05e
-- title:
--   Lemma 6.2, p.21 — $\iota_\sigma$ is a well-defined involution of opposite parity
-- statement:
--   Let $a\in\mathcal D\subseteq\mathcal C$, $\mathcal T\in\mathfrak T_{\mathcal D,a}$ and $\sigma\in E^\star_{\mathcal T}$ with $\mathcal Q(\sigma)\neq\{a\}$. Then
--   $$
--   \iota_\sigma(\mathcal T)\in\mathfrak T_{\mathcal D,a},\qquad\sigma\in E^\star_{\iota_\sigma(\mathcal T)},\qquad\iota_\sigma(\iota_\sigma(\mathcal T))=\mathcal T,
--   $$
--   and $|\mathcal T|$ and $|\iota_\sigma(\mathcal T)|$ have opposite parity.
--
--   This makes the backward rule at tree states a well-defined pairing.
--
--   Differences from the source:
--   - generalization: stated under the standing assumption (1.1) with c = 1/100 (§2, p.7) → stated for every instance, without (1.1); reason: the statement is combinatorial and does not use (1.1); adding the hypothesis gives the source's statement
--   - encoding: opposite parity → `T.card % 2 ≠ (ι_σ T).card % 2`; reason: the same statement
-- source:
--   Jain, Mizgerd, Pham, A general counting and sampling Lovász local lemma, arXiv:2609.23671 (held file sha256 cd449f83…), Lemma 6.2, p.21

import Mathlib
import Definitions.Def_GenCountSampleLLL_Inst
import Definitions.Def_GenCountSampleLLL_twoTrees

set_option autoImplicit false

open scoped BigOperators ENNReal

namespace GenCountSampleLLL

open Inst

/-- Lemma 6.2, p.21 (Jain, Mizgerd, Pham, *A general counting and sampling Lovász local lemma*, arXiv:2609.23671 (held file sha256 cd449f83…)). For `T ∈ T_{D,a}` and `σ ∈ E⋆_T` with `Q(σ) ≠ {a}`:
`ι_σ(T) ∈ T_{D,a}`, `σ ∈ E⋆_{ι_σ(T)}`, `ι_σ(ι_σ(T)) = T`, and `|T|`, `|ι_σ(T)|` have opposite
parity.

**Formalization Note.** `ι_σ(T) = T △ {d_σ(T)}`, with `d_σ(T)` the last constraint of
`Q(σ) ∖ {a}` examined by the selection procedure on input `T`. The lemma is combinatorial and
holds for every instance, so (1.1) is not assumed. -/
theorem lemma_6_2 (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m) (ha : a ∈ D)
    (T : Finset (Fin I.m)) (hT : T ∈ I.twoTrees D a) (σ : I.Assign) (hσ : σ ∈ I.Estar D a T)
    (hQ : I.Qv D σ ≠ {a}) :
    I.iota D a T σ ∈ I.twoTrees D a ∧ σ ∈ I.Estar D a (I.iota D a T σ) ∧
      I.iota D a (I.iota D a T σ) σ = T ∧ T.card % 2 ≠ (I.iota D a T σ).card % 2 := by sorry

end GenCountSampleLLL
