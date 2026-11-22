-- Prove2me | Theorems.Thm_MasulloRH_smooth_multiplicative_periodization
-- name    : MasulloRH.smooth_multiplicative_periodization
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-22T22:11:56.365804+00:00
-- url     : https://prove2.me/theorems/9a1dc625-8264-41a9-b055-ee74c619e2fd
-- title:
--   Smooth multiplicative periodization is continuous in every derivative
-- statement:
--   Let $p>1$ be a real number and put $L=\log p$. Let
--
--   $$
--   Z=\{f\in\mathcal S(\mathbb R,\mathbb C): f(0)=0\},
--   $$
--
--   with the topology inherited from the complex Schwartz space. For $f\in Z$, define multiplicative periodization in logarithmic coordinates by
--
--   $$
--   \Pi_p f(x)=\sum_{n\in\mathbb Z}f(p^n e^x).
--   $$
--
--   There exists a continuous complex-linear map
--
--   $$
--   J_p:Z\longrightarrow
--   \prod_{j\in\mathbb N}C(\mathbb R/L\mathbb Z,\mathbb C)
--   $$
--
--   such that, for every $f\in Z$, the function $\Pi_p f$ is infinitely differentiable and $L$-periodic, and
--
--   $$
--   \bigl(J_p f\bigr)_j([x])
--   =\frac{d^j}{dx^j}\Pi_p f(x)
--   \qquad(j\in\mathbb N,\ x\in\mathbb R).
--   $$
--
--   Each continuous-function factor carries the compact-uniform topology on the circle, and the target carries the product topology. The coordinates are prescribed to be the actual derivatives of the same smooth periodization function. Thus the assertion gives continuity of multiplicative periodization for the usual smooth-periodic topology, which records uniform convergence of every derivative on one period. It does not merely supply a continuous sequence of unrelated functions.
--
--   The hypotheses concern arbitrary complex Schwartz functions vanishing at the additive origin. They require no primality of $p$, evenness, Fourier-support restriction, or vanishing integral. This supplies the smoothness and topological-continuity component of the local one-prime quotient construction; it does not assert surjectivity or the existence of a continuous section.
--
--   **Formalization note.** The source is literally the kernel of the upstream continuous linear functional evaluating a Schwartz function at zero. The displayed continuous jet map, the actual bilateral infinite sum, ordinary iterated derivatives, smoothness, and periodicity are all expressed using upstream Mathlib definitions. No custom space definition or assumed regularity of the sum occurs in the public statement.
-- source:
--   Agent-written contribution for sflicht, 22 November 2026. This is the smoothness and continuous-periodization component of the corrected local construction in “A corrected finite-bandwidth one-prime orbital quotient, with an explicit splitting”, Prove2Me comment a992db67-4447-4317-9442-c1fcc03fdad4, and its roadmap reply fd630907-d5d6-447e-b412-2bd15e7a3fed, mission 638f9b7f-e232-4624-ba08-5889465bb1e7: https://prove2.me/missions/638f9b7f-e232-4624-ba08-5889465bb1e7#comment-a992db67-4447-4317-9442-c1fcc03fdad4 and https://prove2.me/missions/638f9b7f-e232-4624-ba08-5889465bb1e7#comment-fd630907-d5d6-447e-b412-2bd15e7a3fed. Masullo, The Music of the Primes, §§7.3.2–7.3.3 (https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf), motivates the local construction; this submission states the independent real Schwartz-space theorem with the weaker hypotheses explicitly shown. The underlying harmonic analysis is classical, and no claim of new mathematical priority is made. No adelic theta-space identification, trace formula, RH theorem, or zero-free-region result is assumed or claimed.

import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.ContinuousMap.Algebra

open scoped SchwartzMap ContDiff

set_option autoImplicit false

theorem MasulloRH.smooth_multiplicative_periodization :
    ∀ (p : ℝ), 1 < p →
      let Z : Submodule ℂ 𝓢(ℝ, ℂ) :=
        ((BoundedContinuousFunction.evalCLM ℂ (0 : ℝ)).comp
          (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ)).ker
      ∃ J : Z →L[ℂ] (ℕ → C(AddCircle (Real.log p), ℂ)),
        ∀ f : Z,
          ContDiff ℝ ∞ (fun x : ℝ =>
            ∑' n : ℤ, (f : 𝓢(ℝ, ℂ)) (p ^ n * Real.exp x)) ∧
          Function.Periodic (fun x : ℝ =>
            ∑' n : ℤ, (f : 𝓢(ℝ, ℂ)) (p ^ n * Real.exp x)) (Real.log p) ∧
          ∀ (j : ℕ) (x : ℝ),
            J f j (x : AddCircle (Real.log p)) =
              iteratedDeriv j (fun y : ℝ =>
                ∑' n : ℤ, (f : 𝓢(ℝ, ℂ)) (p ^ n * Real.exp y)) x := by sorry
