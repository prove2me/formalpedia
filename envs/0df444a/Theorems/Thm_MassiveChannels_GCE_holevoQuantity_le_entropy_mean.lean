-- Prove2me | Theorems.Thm_MassiveChannels_GCE_holevoQuantity_le_entropy_mean
-- name    : MassiveChannels.GCE.holevoQuantity_le_entropy_mean
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:43:51.243805+00:00
-- url     : https://prove2.me/theorems/70182d75-663b-42a5-b05c-aa29546c6de9
-- title:
--   The Holevo quantity is at most the average-state entropy
-- statement:
--   For a finite ensemble $\mathcal E=\{(p_i,\rho_i)\}$ of density matrices, let $\bar\rho=\sum_i p_i\rho_i$ and let $\chi(\mathcal E)=S(\bar\rho)-\sum_i p_iS(\rho_i)$, where entropy is measured in bits. Then
--
--   $$\chi(\mathcal E)\leq S(\bar\rho).$$
--
--   This is the second inequality in the paper's upper bound on accessible information, and applies to mixed ensemble members as well as pure ones.
--
--   **Formalization Note** The quantum state space is finite-dimensional and nonempty. Ensemble validity requires nonnegative probabilities summing to one and a density matrix at every label, including labels of zero weight.
-- source:
--   Sen(De), Sen, Gromek, Bruß, Lewenstein, Capacities of Quantum Channels for Massive Bosons and Fermions, arXiv:quant-ph/0505028v2, p. 2, ‘Now I_acc(𝓔) ≤ χ(𝓔) ≤ S(ϱ)’

import Mathlib
import Definitions.Def_MassiveChannels_GCE_Model

set_option autoImplicit false

noncomputable section

namespace MassiveChannels.GCE

open QAlgorithms
open QAlgorithms.Papers.Independent.Dependency50.P07

/-- The Holevo quantity cannot exceed the entropy of the average state. -/
theorem holevoQuantity_le_entropy_mean {X Q : Type} [Fintype X] [Fintype Q]
    [DecidableEq Q] [Nonempty Q] (e : CQData X Q) (he : e.Valid) :
    ensembleInformation e ≤ vnEntropy (ensembleMean e) := by sorry

end MassiveChannels.GCE
