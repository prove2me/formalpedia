-- Prove2me | Theorems.Thm_KServer_three_server_of_semiLazy_le_lazy
-- name    : KServer.three_server_of_semiLazy_le_lazy
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T17:16:31.215861+00:00
-- url     : https://prove2.me/theorems/2d29abc0-ac30-403a-ae92-3efb0478aff1
-- title:
--   Three servers are 3-competitive on any space where the semi-lazy potential is redundant
-- statement:
--   Let $M$ be **any** metric space. If
--
--   $$\hat\Psi_{w,r} \;\le\; \Psi_{w,r}$$
--
--   for every work function $w$ over $M$ with last request $r$ — that is, if the two auxiliary potentials $\Lambda$ and $\Gamma$ never exceed the lazy potential — then the three-server problem on $M$ admits a $3$-competitive online algorithm from any initial configuration.
--
--   ## Role
--
--   This is the theorem that turns the whole potential-function machinery into a competitiveness result, and it reduces the three-server problem on a given space to a single, purely local inequality between three explicitly defined suprema. It is the form in which Bein, Chrobak and Larmore state their main tool: they verify the hypothesis for the Manhattan plane, obtaining the $3$-competitiveness of the Work Function Algorithm there, and remark that the same property holds for every six-point space.
--
--   The proof combines three ingredients. The lazy potential itself is used as the potential function. Its **offset property** is immediate from the lower bound
--   $$\Psi_{w,r} \;\ge\; ra + rb + ab - 4\,w(r,a,b),$$
--   applied at a configuration on which $w$ is (nearly) minimised — such a configuration may be taken to contain $r$, since moving a server to the last request can only decrease the work function. Its **update property** unwinds as
--   $$\Psi_{\mu,s} + r_s(w) \;=\; \hat\mu(s) + \dot\mu(s) + r_s(w) \;=\; \hat w(s) + \dot w(s) \;=\; \Psi_{w,s} \;\le\; \hat\Psi_{w,r} \;\le\; \Psi_{w,r},$$
--   where the second equality is Corollary 1 for the shadow term and the invariance of $\dot w$ under the request $s$ — every configuration occurring in $\dot w(s)$ contains $s$, and there $\mu$ and $w$ agree. The penultimate inequality is the twelve-case lemma, and the last is the hypothesis. The potential criterion then delivers the algorithm.
--
--   **Formalization note.** The potential is $\Phi_\tau = \Psi_{w_\tau, \text{last}(\tau)}$, with the empty history handled by observing that requesting a point already occupied by a server of the initial configuration changes neither the work function nor the potential; so the initial work function is itself a work function with a last request, and the telescoping starts there rather than at an undefined $\Phi_0$. The injective configuration $X_0$ is what the extended cost lemma requires of the space.
-- source:
--   W. Bein, M. Chrobak, L. Larmore, The 3-Server Problem in the Plane, Theoretical Computer Science 289(1) (2002) 335-354, Theorem 1: 'Let M be any metric space. If hatPsi_{w,r} <= Psi_{w,r} for every work function w over M with last request r, then WFA for 3 servers on M is 3-competitive.'

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_lazy_potential

namespace KServer

theorem three_server_of_semiLazy_le_lazy (M : Type) [MetricSpace M] (C₀ X₀ : Config 3 M)
    (hX₀ : Function.Injective X₀)
    (hspace : ∀ (σ : List M) (r : M),
      semiLazyPot C₀ (σ ++ [r]) r ≤ lazyPot C₀ (σ ++ [r]) r) :
    ∃ A : OnlineAlgorithm 3 M, A.conf [] = C₀ ∧ IsCompetitive A 3 := by sorry

end KServer
