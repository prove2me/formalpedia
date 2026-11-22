-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSearch_coherent_gaussian_ticket_preparation
-- name    : InfoLossLAR.WorstCase.RegevSearch.coherent_gaussian_ticket_preparation
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-21T06:10:29.213825+00:00
-- url     : https://prove2.me/theorems/eb71f18d-fcb6-4319-86d8-2f1dc7f5d60d
-- title:
--   Coherent finite-gate preparation of truncated Gaussian tickets with retries
-- statement:
--   Fix a polynomial-time generator of finite-precision requests for a one-dimensional Gaussian. Two positive synthesis and interpretation constants suffice for every request word. Let $s\ge1$ be its standard width parameter, whose square is the prescribed variance, and let $F\ge2$ denote the request's truncation factor. Give the binary ticket register enough capacity for the truncated integer interval and the header enough space for the request. For any positive retry count $m$, the finite gate circuit begins in the prescribed classical basis state and produces a unit vector $\psi$. There is a unit spectator state $\chi$ for which
--   $$\left\|\psi-J(\gamma_s\otimes\chi)\right\|_2\le m\delta+2\exp\!\left(-\frac{m}{112F}\right).$$
--   Here $\gamma_s$ is the normalized truncated Gaussian ticket state, $J$ embeds the selected ticket and the retained registers into the full qubit space, and $\delta$ is the single-trial error given by the numerical and gate-synthesis budgets. This provides a coherent Gaussian source with a uniform choice of synthesis constants as the ticket width and accuracy vary.
-- source:
--   One-dimensional coherent Gaussian preparation used in https://prove2.me/theorems/912efb88-48a6-4e10-b841-1070dd0ad365

import Definitions.Def_InfoLossLAR_CoherentGaussianTickets
set_option autoImplicit false
open QAlgorithms.Complexity OAI.MetricKMedian.Binary.Automatic
open InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide
open InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.Padding

theorem InfoLossLAR.WorstCase.RegevSearch.coherent_gaussian_ticket_preparation
    (request : Str → PointRequest × List Unit) (hr : Poly request)
    (hp : ∀ a : ℕ, Poly (Builder.gateWord request a)) :
    RegisteredTrial.contract request hp := by sorry
