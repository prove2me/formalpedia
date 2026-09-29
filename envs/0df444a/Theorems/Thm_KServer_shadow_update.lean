-- Prove2me | Theorems.Thm_KServer_shadow_update
-- name    : KServer.shadow_update
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T17:08:33.496711+00:00
-- url     : https://prove2.me/theorems/552ac60e-b899-45e4-b3f8-3c2f00510845
-- title:
--   The shadow absorbs the pseudocost of a request
-- statement:
--   Let $w$ be a work function and let $\mu = w^s$ be its update after a request at $s$. Write
--
--   $$r_s(w) \;=\; \sup_X \bigl\{\,\mu(X) - w(X)\,\bigr\}$$
--
--   for the *pseudocost* of the request — the largest amount by which requesting $s$ can raise the work function. Then the shadow at $s$ absorbs exactly that much:
--
--   $$\hat\mu(s) + r_s(w) \;=\; \hat w(s).$$
--
--   ## Role
--
--   This identity is the reason the shadow is the right first ingredient of a potential function. In the update property required of a potential,
--
--   $$\Phi_{\mu,s} + r_s(w) \;\le\; \Phi_{w,r},$$
--
--   the pseudocost term is the one that has to be paid for, and this corollary pays for it outright: the shadow component of $\Phi_{\mu,s}$, taken together with $r_s(w)$, is *equal* to the shadow component evaluated against the old work function. Everything else in the potential is unchanged by the request, because the remaining terms only involve configurations that contain $s$, on which $\mu$ and $w$ agree. What is left is a comparison of the potential at $s$ with the potential at the previous request, which is a separate matter.
--
--   The identity is a direct consequence of the duality lemma of Koutsoupias and Papadimitriou: an $(w,s)$-maximizer $A$ of the shadow is also an $(\mu,s)$-maximizer, and simultaneously maximizes $\mu(\cdot) - w(\cdot)$. Then
--
--   $$\hat\mu(s) + r_s(w) = \Bigl(\sum_{a \in A} sa - \mu(A)\Bigr) + \bigl(\mu(A) - w(A)\bigr) = \sum_{a \in A} sa - w(A) = \hat w(s),$$
--
--   the two occurrences of $\mu(A)$ cancelling. That the *same* configuration realises both maxima is the whole content.
--
--   **Formalization note.** Suprema over configurations need not be attained in a general metric space, so the statement is split into the two inequalities that together say the identity holds, with the direction that would need an exact maximizer stated up to an arbitrary $\varepsilon$. The proof correspondingly uses an approximate form of the duality lemma, applied to an $\varepsilon$-maximizer of the shadow.
-- source:
--   W. Bein, M. Chrobak, L. Larmore, The 3-Server Problem in the Plane, Theoretical Computer Science 289(1) (2002) 335-354, Corollary 1: 'Given a work function w, let mu = w^s for some s in M. Then hat-mu(s) + r_s(w) = hat-w(s).' It is derived there from Lemma 1, the duality lemma of E. Koutsoupias and C. Papadimitriou, On the k-server conjecture, JACM 42(5) (1995) 971-983.

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_lazy_potential

namespace KServer

theorem shadow_update (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (s : M) :
    (∀ X : Config k M,
      shadow C₀ (σ ++ [s]) s + workFnU C₀ (σ ++ [s]) X
        ≤ shadow C₀ σ s + workFnU C₀ σ X)
    ∧ (∀ ε : ℝ, 0 < ε → ∃ A : Config k M,
      shadow C₀ σ s ≤ shadow C₀ (σ ++ [s]) s
        + (workFnU C₀ (σ ++ [s]) A - workFnU C₀ σ A) + ε) := by sorry

end KServer
