-- Prove2me | Theorems.Thm_GGHRSW_ColoredMatrix_theorem_6
-- name    : GGHRSW.ColoredMatrix.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:07:49.199633+00:00
-- url     : https://prove2.me/theorems/b4acc17f-e372-4ecf-bd1d-45de8c5946df
-- title:
--   Theorem 6, p. 38 — equivalent partial assignments give O(nT²/p)-close views in the generic colored matrix model
-- statement:
--   Let $p$ be a prime, $BP$ a length-$n$ branching program over $\ell$ input bits, and $(J,\sigma)$, $(J,\sigma')$ two partial input assignments on the same set $J$ of positions that are functionally equivalent: $F|_\sigma = F|_{\sigma'}$. Let $\mathcal A$ be an adversary in the generic colored matrix model that makes $q$ adaptive queries to the representation oracle initialized with $DB(p,BP,(J,\sigma))$, respectively $DB(p,BP,(J,\sigma'))$, built from a fresh sample of $\mathcal{RND}_p(BP)$. Let $T = |DB| + q$ bound the number of handles it receives. Then there is an absolute constant $C$, independent of $p$, $BP$, the assignments and $\mathcal A$, such that
--   $$\Big|\Pr\big[\mathcal A^{DB(p,BP,(J,\sigma))}=1\big] - \Pr\big[\mathcal A^{DB(p,BP,(J,\sigma'))}=1\big]\Big| \le \frac{C\,n\,T^2}{p}.$$
--   Equivalently, the statistical distance between the views $\mathsf{view}_{\mathcal A}(p,BP,(J,\sigma),T)$ and $\mathsf{view}_{\mathcal A}(p,BP,(J,\sigma'),T)$ is $O(nT^2/p)$.
--
--   This is the paper's unconditional evidence for its Equivalent Program Indistinguishability assumption (Assumption 1): no attack that only adds, scales and multiplies the garbled matrices in an order respecting their colours can tell two functionally equivalent input fixings apart, except with probability $O(nT^2/p)$.
--
--   **Formalization Note.** The constant $C$ is quantified before everything else, which is what $O(\cdot)$ means here; no value is fixed. The statistical distance is expressed as the largest acceptance gap: the adversary includes its final decision, so quantifying over every adversary covers every distinguisher of the views (coins included). The page's $T$ counts all handles sent, initial ones included; a $q$-query adversary receives at most $|DB|+q$ handles, the value used. The bundling scalars follow the $\gamma$-procedure of p. 42, and the output convention is "identity means 1"; see the definitions file. The sentence before the theorem says $O(t^2/p)$; the theorem's $O(nT^2/p)$ is used.
-- source:
--   Garg, Gentry, Halevi, Raykova, Sahai and Waters, Candidate Indistinguishability Obfuscation and Functional Encryption for All Circuits, SIAM J. Comput. 45(3), 2016 (authors' version of July 21, 2013), p. 38, Theorem 6

import Mathlib
import Definitions.Def_GGHRSW_ColoredMatrix_Model

namespace GGHRSW.ColoredMatrix

theorem theorem_6 : ∃ C : ℝ, ∀ (p : ℕ) [Fact p.Prime] (bp : BP) (J : Finset (Fin bp.ℓ))
    (σ σ' : Fin bp.ℓ → Bool), FunctionallyEquivalent bp J σ σ' →
    ∀ A : Adversary p,
      |acceptProb p bp J σ A - acceptProb p bp J σ' A| ≤
        C * bp.n * ((dbSize bp J + A.q : ℕ) : ℝ) ^ 2 / p := by sorry

end GGHRSW.ColoredMatrix
