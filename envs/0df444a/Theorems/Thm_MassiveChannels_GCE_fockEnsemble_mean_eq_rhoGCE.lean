-- Prove2me | Theorems.Thm_MassiveChannels_GCE_fockEnsemble_mean_eq_rhoGCE
-- name    : MassiveChannels.GCE.fockEnsemble_mean_eq_rhoGCE
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:43:44.419994+00:00
-- url     : https://prove2.me/theorems/23d35c64-594b-447c-b043-5b6566bf236e
-- title:
--   The grand-canonical state is the mean of its Fock-state ensemble
-- statement:
--   Let $\mathcal H$ and $\hat N$ be commuting Hermitian operators on a finite-dimensional nonzero complex Hilbert space. Then a joint orthonormal eigenbasis of $\mathcal H$ and $\hat N$ exists. Moreover, for real $\beta$ and $\mu$ and **every** joint orthonormal eigenbasis $\{v_j\}$, the pure-state ensemble with weights $p_j=\langle v_j,\rho_{\mathrm{GCE}}v_j\rangle$ is a valid ensemble and has mean
--
--   $$\sum_j p_j|v_j\rangle\langle v_j|=\rho_{\mathrm{GCE}}.$$
--
--   Thus the grand-canonical state is realized by orthogonal Fock states, giving an admissible ensemble at its own mean energy and mean particle number.
--
--   **Formalization Note** The paper's occupation-number basis is represented by simultaneous eigenvectors of the two commuting matrices. The weights are Born probabilities obtained from the real trace of a rank-one projector times the GCE density matrix.
-- source:
--   Sen(De), Sen, Gromek, Bruß, Lewenstein, Capacities of Quantum Channels for Massive Bosons and Fermions, arXiv:quant-ph/0505028v2, p. 2, ‘Again the ensemble elements are pure and orthogonal (Fock states)’

import Mathlib
import Definitions.Def_MassiveChannels_GCE_Model

set_option autoImplicit false

noncomputable section

namespace MassiveChannels.GCE

open QAlgorithms
open QAlgorithms.Papers.Independent.Dependency50.P07

/-- A joint eigenbasis of `Ham` and `Nop` exists, and for every such basis the GCE is the
average of its pure, orthogonal basis (Fock) states with the Born weights. -/
theorem fockEnsemble_mean_eq_rhoGCE {Q : Type} [Fintype Q] [DecidableEq Q]
    [Nonempty Q] (Ham Nop : Matrix Q Q ℂ) (hH : Ham.IsHermitian)
    (hN : Nop.IsHermitian) (hcomm : Ham * Nop = Nop * Ham) (beta mu : ℝ) :
    (∃ v : OrthonormalBasis Q ℂ (EuclideanSpace ℂ Q), IsJointEigenbasis Ham Nop v) ∧
    ∀ v : OrthonormalBasis Q ℂ (EuclideanSpace ℂ Q), IsJointEigenbasis Ham Nop v →
      (fockEnsemble (rhoGCE Ham Nop beta mu) v).Valid ∧
      ensembleMean (fockEnsemble (rhoGCE Ham Nop beta mu) v) =
        rhoGCE Ham Nop beta mu := by sorry

end MassiveChannels.GCE
