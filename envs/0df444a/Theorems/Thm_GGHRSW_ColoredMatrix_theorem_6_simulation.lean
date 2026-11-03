-- Prove2me | Theorems.Thm_GGHRSW_ColoredMatrix_theorem_6_simulation
-- name    : GGHRSW.ColoredMatrix.theorem_6_simulation
-- status  : Proved
-- author  : @Victorized
-- created : 2026-11-03T00:26:30.103708+00:00
-- url     : https://prove2.me/theorems/66f48dd0-0601-4df9-a07e-c00ff14402aa
-- title:
--   Proof of Theorem 6, App. C.3 — the view is determined by the coins and $F|_\sigma$ except with probability $O(nT^2/p)$
-- statement:
--   Let $p$ be a prime, $BP$ an oblivious branching program of length $n\ge 1$ over $\ell$ input bits, $J\subseteq[\ell]$ a set of input positions, and $\mathcal A$ an adversary in the generic colored matrix model with random coins $c$ that makes $q$ adaptive queries. For a partial assignment $\sigma$ of the bits in $J$, write
--
--   1. $F|_\sigma$ for the restricted function $x\mapsto BP(x \text{ with the bits in } J \text{ set by } \sigma)$ on $\{0,1\}^\ell$;
--   2. $\mathsf{view}_{\mathcal A}(c,\omega;\sigma)$ for the sequence of replies that $\mathcal A$, run with coins $c$, receives from the representation oracle initialized with $DB(p,BP,(J,\sigma))$, built from the sample $\omega$ of $\mathcal{RND}_p(BP)$;
--   3. $T=|DB|+q$ for the bound on the number of handles $\mathcal A$ receives.
--
--   Then there is an absolute constant $C$, independent of $p$, $BP$, $J$ and $\mathcal A$, with the following property. For every $p$, $BP$, $J$ and $\mathcal A$ there is a simulator $\mathcal S$, a map that takes a Boolean function $f$ on $\{0,1\}^\ell$ and coins $c$ and outputs a reply sequence, such that for every assignment $\sigma$ of the bits in $J$
--   $$\Pr_{c,\,\omega}\Big[\mathsf{view}_{\mathcal A}(c,\omega;\sigma)\neq \mathcal S\big(F|_\sigma,\,c\big)\Big]\;\le\;\frac{C\,n\,T^2}{p}.$$
--
--   In words: except with probability $O(nT^2/p)$, everything the adversary learns from the oracle is a deterministic function of its own coins and of the restricted function $F|_\sigma$; the randomized matrices reveal nothing beyond $F|_\sigma$. Since functionally equivalent assignments satisfy $F|_\sigma=F|_{\sigma'}$, this is the simulation statement behind Theorem 6 (p. 38). It isolates the collision analysis of the proof in App. C.3 from the final averaging step, and it is the natural target for that analysis.
--
--   **Formalization Note.** The probability is over uniform coins in $\mathrm{Fin}\,K$ and a uniform sample of the finite sample space, as in `acceptProb`. The simulator receives the restricted function as a whole rather than oracle access to it, and its efficiency is not tracked; the statement is information-theoretic, as Theorem 6 is. The constant is quantified first, which is what $O(\cdot)$ means. The hypothesis $n\ge 1$ is necessary: for $n=0$ the right-hand side is $0$, while the view is still random (whether $\langle\mathbf s^*,\mathbf t^*\rangle=0$ is visible to the adversary and has probability about $1/p$). Theorem 6 for $n=0$ needs no simulation, because then the database does not depend on $\sigma$.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from Claude (Anthropic).
-- source:
--   Garg, Gentry, Halevi, Raykova, Sahai and Waters, Candidate Indistinguishability Obfuscation and Functional Encryption for All Circuits, SIAM J. Comput. 45(3), 2016 (authors' version of July 21, 2013), App. C.3, proof of Theorem 6, pp. 38–43 (simulation step behind Theorem 6, p. 38)

import Mathlib
import Definitions.Def_GGHRSW_ColoredMatrix_Model

namespace GGHRSW.ColoredMatrix

theorem theorem_6_simulation : ∃ C : ℝ, ∀ (p : ℕ) [Fact p.Prime] (bp : BP), 0 < bp.n →
    ∀ (J : Finset (Fin bp.ℓ)) (A : Adversary p),
    ∃ Sim : ((Fin bp.ℓ → Bool) → Bool) → Fin A.K → List (Option ℕ),
      ∀ σ : Fin bp.ℓ → Bool,
        ((Finset.univ.filter fun x : Fin A.K × Sample p bp =>
            view bp J σ A x.1 x.2 ≠ Sim (fun χ => bp.eval (fix J σ χ)) x.1).card : ℝ) /
          Fintype.card (Fin A.K × Sample p bp) ≤
        C * bp.n * ((dbSize bp J + A.q : ℕ) : ℝ) ^ 2 / p := by sorry

end GGHRSW.ColoredMatrix
