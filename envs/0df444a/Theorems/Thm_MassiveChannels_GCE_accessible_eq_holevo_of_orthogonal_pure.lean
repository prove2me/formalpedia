-- Prove2me | Theorems.Thm_MassiveChannels_GCE_accessible_eq_holevo_of_orthogonal_pure
-- name    : MassiveChannels.GCE.accessible_eq_holevo_of_orthogonal_pure
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:43:41.329565+00:00
-- url     : https://prove2.me/theorems/bea7a125-400e-4a9a-ac71-fa638d6898e4
-- title:
--   Orthogonal pure states transmit their full label entropy
-- statement:
--   Let $\{v_j\}$ be an orthonormal basis of a nonzero finite-dimensional quantum system, and let $p$ be any probability distribution on its labels. Form the ensemble $\mathcal E=\{(p_j,|v_j\rangle\langle v_j|)\}$. Then it is valid and
--
--   $$I_{\mathrm{acc}}(\mathcal E)=\chi(\mathcal E)=H(p)=S(\bar\rho),$$
--
--   where $\bar\rho$ is the mean state and all information and entropy quantities are in bits. This establishes the information available from the Fock-state ensemble used for capacity attainment.
--
--   **Formalization Note** The paper explicitly gives $I_{\mathrm{acc}}=\chi=\log_2 d$ for uniform weights on $d$ orthogonal pure states. Its grand-canonical application requires nonuniform weights, so the statement records that weighted case for a complete basis.
-- source:
--   Sen(De), Sen, Gromek, Bruß, Lewenstein, Capacities of Quantum Channels for Massive Bosons and Fermions, arXiv:quant-ph/0505028v2, p. 2, ‘If the pure states are orthogonal, I_acc = χ = log₂ d’ and ‘the channel capacity is reached by the same ensemble’

import Mathlib
import Definitions.Def_MassiveChannels_GCE_Model

set_option autoImplicit false

noncomputable section

namespace MassiveChannels.GCE

open QAlgorithms
open QAlgorithms.Papers.Independent.Dependency50.P07
open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

/-- Orthogonal pure states transmit their full classical label entropy. -/
theorem accessible_eq_holevo_of_orthogonal_pure {Q : Type} [Fintype Q]
    [DecidableEq Q] [Nonempty Q]
    (v : OrthonormalBasis Q ℂ (EuclideanSpace ℂ Q)) (p : Q → ℝ)
    (hp : (∀ j, 0 ≤ p j) ∧ (∑ j, p j) = 1) :
    let e : CQData Q Q := ⟨p, fun j => pureDensity (v j)⟩
    e.Valid ∧ accessibleInformation e = ensembleInformation e ∧
      ensembleInformation e = shannon p ∧
      shannon p = vnEntropy (ensembleMean e) := by sorry

end MassiveChannels.GCE
