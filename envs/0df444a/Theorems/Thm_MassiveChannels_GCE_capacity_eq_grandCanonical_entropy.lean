-- Prove2me | Theorems.Thm_MassiveChannels_GCE_capacity_eq_grandCanonical_entropy
-- name    : MassiveChannels.GCE.capacity_eq_grandCanonical_entropy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:43:59.473817+00:00
-- url     : https://prove2.me/theorems/cd246196-a105-4dbd-aedd-9f40adcaddef
-- title:
--   The two-constraint channel capacity equals grand-canonical entropy and is attained by Fock states
-- statement:
--   Let $\mathcal H$ and $\hat N$ be commuting Hermitian operators on a nonzero finite-dimensional complex Hilbert space. For real $\beta$ and $\mu$, put $\rho_{\mathrm{GCE}}=\exp[-\beta(\mathcal H-\mu\hat N)]/Z$, $E=\operatorname{tr}(\rho_{\mathrm{GCE}}\mathcal H)$, and $N=\operatorname{tr}(\rho_{\mathrm{GCE}}\hat N)$. Among all finite ensembles of density matrices whose mean state has exactly these expectations, the greatest accessible information is
--
--   $$C_{E,N}=S(\rho_{\mathrm{GCE}}).$$
--
--   Moreover, a joint orthonormal eigenbasis of $\mathcal H$ and $\hat N$, weighted by its grand-canonical probabilities, gives an admissible Fock-state ensemble whose accessible information equals this capacity. The result identifies both the value and a capacity-attaining input ensemble.
--
--   **Formalization Note** The system is finite-dimensional, exact for finitely many fermionic levels and a truncation for bosons. The capacity ranges over every finite ensemble size, arbitrary mixed density matrices and all finite POVMs. Constraints are equalities. The real parameters $\beta$ and $\mu$ are unrestricted; $E$ and $N$ are constructed from the GCE rather than assumed to admit an inverse parameterization.
-- source:
--   Sen(De), Sen, Gromek, Bruß, Lewenstein, Capacities of Quantum Channels for Massive Bosons and Fermions, arXiv:quant-ph/0505028v2, p. 2, ‘The channel capacity C_{E,N} ... is the maximum of I_acc(𝓔)’ through ‘reached by the same ensemble’; abstract p. 1 and conclusion p. 4

import Mathlib
import Definitions.Def_MassiveChannels_GCE_Model

set_option autoImplicit false

noncomputable section

namespace MassiveChannels.GCE

open QAlgorithms
open QAlgorithms.Papers.Independent.Dependency50.P07

/-- The two-constraint capacity equals the GCE entropy and is attained by Fock states. -/
theorem capacity_eq_grandCanonical_entropy {Q : Type} [Fintype Q] [DecidableEq Q]
    [Nonempty Q] (Ham Nop : Matrix Q Q ℂ) (hH : Ham.IsHermitian)
    (hN : Nop.IsHermitian) (hcomm : Ham * Nop = Nop * Ham) (beta mu : ℝ) :
    let rho := rhoGCE Ham Nop beta mu
    IsGreatest (capacityValues Ham Nop (expect Ham rho) (expect Nop rho))
      (vnEntropy rho) ∧
    ∃ v : OrthonormalBasis Q ℂ (EuclideanSpace ℂ Q),
      IsJointEigenbasis Ham Nop v ∧
      Admissible Ham Nop (expect Ham rho) (expect Nop rho) (fockEnsemble rho v) ∧
      accessibleInformation (fockEnsemble rho v) = vnEntropy rho := by sorry

end MassiveChannels.GCE
