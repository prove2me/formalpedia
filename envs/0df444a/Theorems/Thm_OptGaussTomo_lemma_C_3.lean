-- Prove2me | Theorems.Thm_OptGaussTomo_lemma_C_3
-- name    : OptGaussTomo.lemma_C_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:06:37.744048+00:00
-- url     : https://prove2.me/theorems/2c5283b3-a1af-420a-b6f4-7763d3e99cfd
-- title:
--   Lemma C.3 — $\sigma^{\otimes n}$ lies in the span of $\{U_R^{\otimes n}\}$
-- statement:
--   If $\sigma$ is an $m$-mode fermionic Gaussian state, then for every $n$
--
--   $$
--   \sigma^{\otimes n}\in\mathbb C\{U_R^{\otimes n}: R\in SO(2m)\},
--   $$
--
--   the complex linear span of the $n$-fold tensor powers of fermionic Gaussian unitaries. Together with the general random purification theorem this yields Corollary 4.1.
--
--   Differences from the source:
--   - encoding: ℂ{U_R^{⊗n} : R ∈ SO(2m)} → the complex linear span of U^{⊗n} over all fermionic Gaussian unitaries U; reason: finite dimension, so the span is closed and is the algebra generated; phases of U_R do not change the span
-- source:
--   Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, Optimal tomography of bosonic and fermionic Gaussian states, arXiv:2607.11847 (held version, sha256 0f7548a2a5cfd55079e5d7f1787c97c8561a818a53d7e29824715104bad416ed), Lemma C.3 p.36 (pdf p.36)

import Mathlib
import Definitions.Def_FermiCap_Gaussian_States
import Definitions.Def_WildeQIT_Schumacher_tensorPow
import Definitions.Def_OptGaussTomo_IsFermiGaussUnitary

open FermiCap.Gaussian (Qubits Op IsEvenGaussian)

namespace OptGaussTomo

/-- **Lemma C.3** (Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, *Optimal tomography of
bosonic and fermionic Gaussian states*, arXiv:2607.11847, held version, sha256 0f7548a2…, Lemma C.3,
p.36). If `σ` is an `m`-mode fermionic Gaussian state, then `σ^{⊗n} ∈ ℂ{U_R^{⊗n} : R ∈ SO(2m)}`.

**Formalization Note.** `ℂ{…}` is the complex linear span; the space of operators on
`(ℂ²)^{⊗mn}` is finite-dimensional, so it is closed and equals the algebra generated (the set is
closed under products). `U_R` ranges over all Gaussian unitaries (`IsFermiGaussUnitary`, (C.1));
the phase of `U_R` does not change the span. `σ^{⊗n}` and `U^{⊗n}` are `tensorPow n`. -/
theorem lemma_C_3 (m n : ℕ) (σ : Op m) (hσ : IsEvenGaussian σ) :
    WildeQIT.Schumacher.tensorPow n σ ∈ Submodule.span ℂ
      {M | ∃ U : Op m, IsFermiGaussUnitary U ∧ M = WildeQIT.Schumacher.tensorPow n U} := by sorry

end OptGaussTomo
