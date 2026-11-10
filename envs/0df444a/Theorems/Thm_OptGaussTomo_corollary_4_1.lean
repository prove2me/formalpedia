-- Prove2me | Theorems.Thm_OptGaussTomo_corollary_4_1
-- name    : OptGaussTomo.corollary_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:07:48.968502+00:00
-- url     : https://prove2.me/theorems/74d5c2d1-01c1-43da-b7a4-8c934616093b
-- title:
--   Corollary 4.1 — fermionic Gaussian random purification channel
-- statement:
--   For all $m$ and $n$ there is a quantum channel $\mathcal P^{\mathrm{Fermi}}_{n,m}$ from $(\bigwedge\mathbb C^m)^{\otimes n}$ to $(\bigwedge\mathbb C^{2m})^{\otimes n}$ such that for every fermionic Gaussian state $\sigma$ on $\bigwedge\mathbb C^m$,
--
--   $$
--   \mathcal P^{\mathrm{Fermi}}_{n,m}[\sigma^{\otimes n}]=\int\big((I\otimes U)\psi^{\mathrm{std}}_\sigma(I\otimes U^\dagger)\big)^{\otimes n}\,dU ,
--   $$
--
--   the integral over the Haar probability measure on fermionic Gaussian unitaries $U$ acting on the purifying copy. The right-hand side is the expectation of $\psi_\sigma^{\otimes n}$ over the random Gaussian purifications $\psi_\sigma=(I\otimes U)\psi^{\mathrm{std}}_\sigma$ of $\sigma$. Composed with a pure-state tomography protocol, this reduces mixed-state to pure-state tomography (Theorem 4.2).
--
--   Differences from the source:
--   - encoding: a channel → a map with a finite normalized Kraus family (published QAlgorithms.IsChannel); reason: in finite dimension these are exactly the completely positive trace-preserving maps
--   - encoding: ∫_{SO(2m)} … dR over the Haar measure of SO(2m) → integral over the compact group of fermionic Gaussian unitaries with its Haar probability measure, entry by entry; reason: U_R is determined by R up to a phase and the integrand is phase invariant
--   - encoding: E over Gaussian purifications ψ_σ of ψ_σ^{⊗n} → not stated separately; reason: the paper defines it as the right-hand integral ('as in the right-hand side formula'); it is the same object
-- source:
--   Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, Optimal tomography of bosonic and fermionic Gaussian states, arXiv:2607.11847 (held version, sha256 0f7548a2a5cfd55079e5d7f1787c97c8561a818a53d7e29824715104bad416ed), Corollary 4.1 p.11 (pdf p.11)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_FermiCap_Gaussian_States
import Definitions.Def_WildeQIT_Schumacher_tensorPow
import Definitions.Def_OptGaussTomo_fermiHaar
import Definitions.Def_OptGaussTomo_stdPurification

open FermiCap.Gaussian (Qubits Op IsEvenGaussian)
open MeasureTheory

namespace OptGaussTomo

/-- **Corollary 4.1** (Fermionic Gaussian random purification; Chen, Fanizza, Girardi, Lami, Mele,
Walter, Witteveen, *Optimal tomography of bosonic and fermionic Gaussian states*, arXiv:2607.11847,
held version, sha256 0f7548a2…, Corollary 4.1, p.11). For all `m` and `n` there is a channel
`P^Fermi_{n,m}` from `(⋀ℂ^m)^{⊗n}` to `(⋀ℂ^{2m})^{⊗n}` such that for every fermionic Gaussian state
`σ` on `⋀ℂ^m`,
`P^Fermi_{n,m}[σ^{⊗n}] = E_{ψ_σ Gaussian purification of σ} ψ_σ^{⊗n}
  = ∫_{SO(2m)} (I ⊗ U_R^{⊗n}) ψ^{std,⊗n}_σ (I ⊗ U_R^{†,⊗n}) dR`.

**Formalization Note.** A channel is the published `QAlgorithms.IsChannel` (a finite normalized
Kraus family; in finite dimension exactly the completely positive trace-preserving maps).
`I ⊗ U` acts on the purifier (last `m` of `2m` qubits, `kronQ 1 U`); applying it to each of the
`n` copies of `ψ^std_σ` gives `((I ⊗ U)ψ^std_σ)^{⊗n}`, whose projector is
`tensorPow n (|w⟩⟨w|)`, `w = (I ⊗ U)ψ^std_σ`. The integral over `SO(2m)` with its Haar probability
measure is taken over the group of Gaussian unitaries with its Haar probability measure
`fermiHaar m` (the integrand is phase invariant; see `fermiHaar`), entry by entry. The middle
expression of the source ("the expectation is taken over the Gaussian purifications obtained by
applying a uniformly random Gaussian unitary `U_R` to the standard purification, as in the
right-hand side formula") is this same integral, so it is not stated separately. -/
theorem corollary_4_1 (m n : ℕ) :
    ∃ P : QAlgorithms.Superop (Fin n → Qubits m) (Fin n → Qubits (2 * m)),
      QAlgorithms.IsChannel P ∧
      ∀ σ : Op m, IsEvenGaussian σ → ∀ a b : Fin n → Qubits (2 * m),
        P (WildeQIT.Schumacher.tensorPow n σ) a b =
          ∫ U : fermiGaussGroup m,
            WildeQIT.Schumacher.tensorPow n (Matrix.vecMulVec ((kronQ 1 (U : Op m)).mulVec (stdPurification σ))
              (star ((kronQ 1 (U : Op m)).mulVec (stdPurification σ)))) a b ∂(fermiHaar m) := by sorry

end OptGaussTomo
