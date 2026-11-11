-- Prove2me | Theorems.Thm_LogConcaveLattice_Lift_claim_I
-- name    : LogConcaveLattice.Lift.claim_I
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:01:41.639511+00:00
-- url     : https://prove2.me/theorems/6286fe5c-1a65-437b-90bb-26c19d0453fe
-- title:
--   Claim I — the maximum of $\Phi_\Lambda(A)=\log\rho_A(\Lambda)/\operatorname{tr}(A)$ over nonzero $A\succcurlyeq0$ is attained
-- statement:
--   This is Claim I inside the proof of Lemma 3.4, in that proof's setting: $\Lambda\subseteq\mathbb R^n$ is a non-zero full-rank lattice with $\det\Lambda\le1$. For a (possibly singular) symmetric positive semidefinite matrix $A$ let $\rho_A(x)=e^{-\pi\langle x,A^+x\rangle}$ for $x\in\operatorname{im}(A)$ and $\rho_A(x)=0$ otherwise, and
--   $$\Phi_\Lambda(A)=\frac{\log\rho_A(\Lambda)}{\operatorname{tr}(A)},\qquad \rho_A(\Lambda)=\sum_{\lambda\in\Lambda}\rho_A(\lambda).$$
--   Then the maximum in
--   $$\Phi^*_\Lambda=\max\{\Phi_\Lambda(A)\mid A\succcurlyeq0,\ A\ne0\}\tag{3.7}$$
--   is attained: there is $A_0\succcurlyeq0$, $A_0\ne0$, with $\Phi_\Lambda(A)\le\Phi_\Lambda(A_0)$ for every $A\succcurlyeq0$, $A\ne0$.
--
--   The maximizer is the matrix of Lemma 3.4; its image is the lattice subspace on which the log-concave lift is first built.
--
--   Differences from the source:
--   - encoding: the claim's setting (the proof of Lemma 3.4 after "without loss of generality we may assume that Λ has full rank") → explicit hypotheses Λ full rank, Λ ≠ {0}, det Λ = covolume Λ ≤ 1; reason: these are the standing assumptions at the point where the claim is made; same instances
-- source:
--   Letwin, Reis, Rothvoss, Strongly Log-Concave Measures and Lattices, STOC 2027 submission #401 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/401.pdf, Claim I in the proof of Lemma 3.4, p. 12 (setting and (3.7) p. 12; proof pp. 12–13)

import Mathlib
import Definitions.Def_LogConcaveLattice_Lift_Lattice
import Definitions.Def_LogConcaveLattice_Lift_Gaussian

namespace LogConcaveLattice.Lift

/-- **Claim I** (p. 12, in the proof of Lemma 3.4, where `Λ` is a non-zero lattice with
`det Λ ≤ 1`, taken of full rank): the maximum in (3.7),
`Φ*_Λ = max {Φ_Λ(A) | A ≽ 0, A ≠ 0}` with `Φ_Λ(A) = log ρ_A(Λ) / tr(A)` and the singular
extension of `ρ_A`, is attained. -/
theorem claim_I (n : ℕ) (Λ : Submodule ℤ (V n)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (hΛ : Λ ≠ ⊥) (hdet : ZLattice.covolume Λ ≤ 1) :
    ∃ A₀ : Matrix (Fin n) (Fin n) ℝ, A₀.PosSemidef ∧ A₀ ≠ 0 ∧
      ∀ A : Matrix (Fin n) (Fin n) ℝ, A.PosSemidef → A ≠ 0 → potential Λ A ≤ potential Λ A₀ := by sorry

end LogConcaveLattice.Lift
