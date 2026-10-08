-- Prove2me | Theorems.Thm_KellyReversibility_Networks_class_queue_reversible_iff
-- name    : KellyReversibility.Networks.class_queue_reversible_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:37:54.867496+00:00
-- url     : https://prove2.me/theorems/ce17cbf3-9220-4a33-b245-9888f6e70f52
-- title:
--   Lemma 3.13 — reversible ⇔ quasi-reversible ⇔ $\Phi(\mathbf n)=\phi_c(\mathbf n)\Phi(\mathbf n-\mathbf e_c)$
-- statement:
--   Consider the queue of Section 3.5 with classes $c=1,\dots,K$: its state is $\mathbf n=(n(1),\dots,n(K))$, class-$c$ customers arrive at rate $\nu(c)>0$, and a class-$c$ customer leaves with intensity $\nu(c)\phi_c(\mathbf n)$, where $\phi_c(\mathbf n)>0$ whenever $n(c)>0$. Suppose the queue is in equilibrium: $\pi$ is a positive function of $\mathbf n$, summing to $1$, which satisfies the equilibrium equations for these rates. Then the following statements are equivalent:
--   1. the process $(n(1),n(2),\dots)$ is reversible, i.e. $\pi(\mathbf n)q(\mathbf n,\mathbf m)=\pi(\mathbf m)q(\mathbf m,\mathbf n)$ for all $\mathbf n,\mathbf m$;
--   2. the queue is quasi-reversible (relations (3.8) and (3.10), with the class counts $n(c)$);
--   3. there exists a positive function $\Phi$ such that, whenever $n(c)>0$,
--   $$\Phi(n(1),\dots,n(c),\dots)=\phi_c(n(1),\dots,n(c),\dots)\,\Phi(n(1),\dots,n(c)-1,\dots)\qquad(3.26).$$
--
--   The function $\Phi$ plays the role of $\pi^{-1}$ up to a constant, and condition (3.26) is the form of state-dependent arrival rates admitted in Theorem 3.14.
--
--   **Formalization Note** Reversibility is read at the rate level as detailed balance (the published `KellyStochasticNetworks.DetailedBalance`); quasi-reversibility is its rate characterization. The book does not say that $\Phi$ is positive, but its proof sets $\pi=b/\Phi$; without positivity $\Phi\equiv0$ would satisfy (3.26) for every queue. Classes are finitely many (`Fin K`); the book allows a countable set.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 89, Lemma 3.13, Eq. (3.26)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyReversibility_Networks_QuasiReversible
import Definitions.Def_KellyReversibility_Networks_ClassCountQueue

namespace KellyReversibility.Networks

/-- **Lemma 3.13** (Kelly 1979, p. 89). For the queue of §3.5 with `K` classes (arrival rates
`ν(c) > 0`, departure intensities `ν(c) φ_c(n)` with `φ_c(n) > 0` whenever `n(c) > 0`) in
equilibrium `π` (positive, summing to `1`, satisfying the equilibrium equations), the following are
equivalent:
1. the process is reversible (`π` and the rates are in detailed balance);
2. the queue is quasi-reversible (rate characterization (3.8), (3.10), class counts `n(c)`);
3. there is a positive function `Φ` with `Φ(n) = φ_c(n) Φ(n - e_c)` whenever `n(c) > 0` (3.26). -/
theorem class_queue_reversible_iff {K : ℕ} (ν : Fin K → ℝ) (φ : Fin K → (Fin K → ℕ) → ℝ)
    (hν : ∀ c, 0 < ν c) (hφ : ∀ c n, 0 < n c → 0 < φ c n)
    (π : (Fin K → ℕ) → ℝ) (hπpos : ∀ n, 0 < π n) (hπsum : HasSum π 1)
    (hπbal : KellyStochasticNetworks.FullBalance π (classCountRates ν φ)) :
    List.TFAE
      [KellyStochasticNetworks.DetailedBalance π (classCountRates ν φ),
       QuasiReversible (classCountRates ν φ) π (fun n c => n c),
       ∃ Φ : (Fin K → ℕ) → ℝ, (∀ n, 0 < Φ n) ∧
         ∀ (n : Fin K → ℕ) (c : Fin K), 0 < n c →
           Φ n = φ c n * Φ (Function.update n c (n c - 1))] := by sorry

end KellyReversibility.Networks
