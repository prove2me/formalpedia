-- Prove2me | Theorems.Thm_OptGaussTomo_lemma_C_1
-- name    : OptGaussTomo.lemma_C_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:06:57.667267+00:00
-- url     : https://prove2.me/theorems/a80f7f5e-3af1-440e-abc2-c93076e97fd7
-- title:
--   Lemma C.1 — $TUT$, $\bar U$, $U^{\mathsf T}$, $U\otimes I$, $I\otimes U$ are Gaussian; the standard purification of a Gaussian state is pure Gaussian in $\mathcal H^+_{2m}$
-- statement:
--   Let $\mathcal H_m$ be the Hilbert space of $m$ fermionic modes, identified with $m$ qubits, and let $T$ be the diagonal change of basis $T|x\rangle=(-1)^{\gamma(x)}|x\rangle$ of §C.2.
--
--   1. If $U$ is a fermionic Gaussian unitary, then $TUT$, $\bar U$ (entrywise complex conjugate) and $U^{\mathsf T}$ are fermionic Gaussian unitaries, and $U\otimes I$ and $I\otimes U$ are fermionic Gaussian unitaries on $\mathcal H_{2m}=\mathcal H_m\otimes\tilde{\mathcal H}_m$.
--   2. If $\rho$ is a fermionic Gaussian state on $\mathcal H_m$, then its standard purification $|\psi^{\mathrm{std}}_\rho\rangle=(\sqrt\rho\otimes I)\sum_x(-1)^{\gamma(x)}|xx\rangle$ is a pure fermionic Gaussian state of even parity on $2m$ modes:
--
--   $$
--   |\psi^{\mathrm{std}}_\rho\rangle\in\mathcal G^+_{2m}.
--   $$
--
--   This is what makes the random purification channel of Corollary 4.1 output Gaussian purifications.
--
--   Differences from the source:
--   - encoding: Ū, Uᵀ and the tensor products, relative to the paper's choice of bases → entrywise conjugate and transpose in the computational basis; A ⊗ B on 2m qubits with the first m qubits the system; reason: the paper's bases (p.34); this identification gives c̃_j = c_j ⊗ I, c̃_{2m+j} = P ⊗ c_j
--   - encoding: a pure Gaussian state in H⁺_{2m} → a unit vector whose projector is an even Gaussian state (IsEvenGaussian) and which has parity +1; reason: the class of OptGaussTomo.gaussVecs; same states
-- source:
--   Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, Optimal tomography of bosonic and fermionic Gaussian states, arXiv:2607.11847 (held version, sha256 0f7548a2a5cfd55079e5d7f1787c97c8561a818a53d7e29824715104bad416ed), Lemma C.1 p.34 (pdf p.34)

import Mathlib
import Definitions.Def_FermiCap_Gaussian_States
import Definitions.Def_OptGaussTomo_IsFermiGaussUnitary
import Definitions.Def_OptGaussTomo_gaussVecs
import Definitions.Def_OptGaussTomo_stdPurification

open FermiCap.Gaussian (Qubits Op IsEvenGaussian)

namespace OptGaussTomo

/-- **Lemma C.1** (Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, *Optimal tomography of
bosonic and fermionic Gaussian states*, arXiv:2607.11847, held version, sha256 0f7548a2…, Lemma C.1,
p.34). Let `H_m` be the Hilbert space of an `m`-mode fermionic system.
1. For a Gaussian unitary `U`, `TUT`, `Ū` and `Uᵀ` are Gaussian unitaries; `U ⊗ I` and `I ⊗ U`
   are Gaussian unitaries on `H_{2m}`.
2. If `ρ` is a Gaussian state, then `|ψ^std_ρ⟩` is a pure Gaussian state in `H⁺_{2m}`.

**Formalization Note.** `T` is the diagonal change of basis `basisChangeT m`
(`T|x⟩ = (−1)^{γ(x)}|x⟩`), `Ū` the entrywise complex conjugate and `Uᵀ` the transpose in the
computational basis (the source's choice of basis, p.34). `U ⊗ I`, `I ⊗ U` are `kronQ U 1`,
`kronQ 1 U` in the identification `H_m ⊗ H̃_m ≅ H_{2m}` (first `m` qubits = system), under which
the doubled Majorana operators are `c̃_j = c_j ⊗ I`, `c̃_{2m+j} = P ⊗ c_j` (p.34). A Gaussian state
is `FermiCap.Gaussian.IsEvenGaussian`; `G⁺_{2m}` is `gaussVecs (2m) true` (unit vectors whose
projector is an even Gaussian state, of even parity). -/
theorem lemma_C_1 (m : ℕ) :
    (∀ U : Op m, IsFermiGaussUnitary U →
      IsFermiGaussUnitary (basisChangeT m * U * basisChangeT m) ∧
      IsFermiGaussUnitary (U.map (starRingEnd ℂ)) ∧
      IsFermiGaussUnitary U.transpose ∧
      IsFermiGaussUnitary (kronQ U 1) ∧
      IsFermiGaussUnitary (kronQ 1 U)) ∧
    (∀ ρ : Op m, IsEvenGaussian ρ → stdPurification ρ ∈ gaussVecs (2 * m) true) := by sorry

end OptGaussTomo
