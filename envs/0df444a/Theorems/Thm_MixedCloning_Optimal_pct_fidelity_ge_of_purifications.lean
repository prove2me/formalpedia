-- Prove2me | Theorems.Thm_MixedCloning_Optimal_pct_fidelity_ge_of_purifications
-- name    : MixedCloning.Optimal.pct_fidelity_ge_of_purifications
-- status  : Proved
-- author  : @dmitry
-- created : 2026-11-22T02:08:30.147751+00:00
-- url     : https://prove2.me/theorems/1c872120-c6dc-467a-b5c0-fc3869ff3937
-- title:
--   Proposition 10, proof step — the PCT fidelity is at least the worst purification bound
-- statement:
--   Fix natural numbers $d,r,n,k$. Let $R$ be a random purification channel, that is, a channel satisfying the specification of Section 2.3:
--
--   $$
--   R\big(\rho^{\otimes n}\big)=\int_{\mathrm U(r)}\Big((I\otimes U)|\rho_0\rangle\langle\rho_0|(I\otimes U^\dagger)\Big)^{\otimes n}dU
--   $$
--
--   for every state $\rho$ of rank at most $r$ and every unit purification $|\rho_0\rangle\in\mathbb C^d\otimes\mathbb C^r$ of $\rho$. Let $\tau$ be any matrix on $(\mathbb C^d\otimes\mathbb C^r)^{\otimes(n+k)}$, let $\mathcal C_W$ be Werner's cloner completed by $\tau$, and let $\mathcal C_{\mathrm{PCT}}=\operatorname{tr}_B\circ\,\mathcal C_W\circ R$ be the PCT map. Let $F$ be the squared fidelity.
--
--   Let $\rho$ be a state on $\mathbb C^d$ of rank at most $r$, and let $c\in\mathbb R$. Suppose that every unit vector $|\psi\rangle\in\mathbb C^d\otimes\mathbb C^r$ with $\operatorname{tr}_B|\psi\rangle\langle\psi|=\rho$ satisfies
--
--   $$
--   c\ \le\ F\Big(\operatorname{tr}_B\,\mathcal C_W\big(|\psi\rangle\langle\psi|^{\otimes n}\big),\ \rho^{\otimes(n+k)}\Big).
--   $$
--
--   Then
--
--   $$
--   c\ \le\ F\Big(\mathcal C_{\mathrm{PCT}}\big(\rho^{\otimes n}\big),\ \rho^{\otimes(n+k)}\Big).
--   $$
--
--   This packages the first steps of the proof of Proposition 10. The PCT output is the expectation, over Haar-random purifications $|\rho\rangle$, of $\operatorname{tr}_B\mathcal C_W(|\rho\rangle\langle\rho|^{\otimes n})$. Concavity of the square-root fidelity [Wat18, Corollary 3.26] then bounds the fidelity of the average from below by the average fidelity. As the source puts it, a bound that holds for all $|\rho\rangle$ therefore transfers to the PCT output.
--
--   **Formalization Note** The specification of $R$ is the platform predicate `IsRPC d r n R`. The hypothesis quantifies over all unit purifications in $\mathbb C^d\otimes\mathbb C^r$, which contains every $(I\otimes U)|\rho_0\rangle$. The bound is stated for squared fidelity; for $c<0$ it is trivial, and for $c\ge0$ it follows from the square-root form.
--
--   Differences from the source:
--   - encoding: the expectation-form inequality for $\sqrt F$ followed by 'since this holds for all $|\rho\rangle$' → a single implication from a pointwise lower bound $c$ to the same bound on the PCT output; reason: this is exactly how the source combines the steps
--   - encoding: Werner's map on the symmetric subspace → the map completed by an arbitrary $\tau$; reason: the completion term vanishes on the random purifications
-- source:
--   Dmitry Grinko, Marco Fanizza, Thilo Scharnhorst, Jack Spilecki, Optimal cloning of mixed states, STOC 2027 submission #243 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/243.pdf, p. 16, proof of Proposition 10: first display (C_PCT(rho^{⊗n}) = E_{|rho>} Tr_B C_W(|rho><rho|^{⊗n})), concavity of the square-root fidelity [Wat18, Corollary 3.26], and 'Since this holds for all |rho>, we obtain ...'; RPC specification from Section 2.3, p. 12.

import Definitions.Def_MixedCloning_Optimal_Model

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace MixedCloning.Optimal
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Proof of Proposition 10 (PDF p.16), first displays: the PCT output is the average over random
purifications of the traced Werner output, so by concavity of the square-root fidelity
[Wat18, Corollary 3.26] a lower bound valid for every purification transfers to the PCT output. -/
theorem pct_fidelity_ge_of_purifications (d r n k : ℕ)
    (R : QAlgorithms.Superop (Word (Fin d) n) (Word (Fin d × Fin r) n)) (hR : IsRPC d r n R)
    (tau : Op (Word (Fin d × Fin r) (n+k)))
    (rho : Op (Fin d)) (hrho : IsState rho) (hrank : rho.rank ≤ r) (c : ℝ)
    (hc : ∀ u : EuclideanSpace ℂ (Fin d × Fin r), ‖u‖ = 1 →
      (fun i j => ∑ z : Fin r, pure u (i,z) (j,z)) = rho →
      c ≤ fidelity (partialTrace (n+k) (werner (Fin d × Fin r) n k tau (tensorPower n (pure u))))
        (tensorPower (n+k) rho)) :
    c ≤ fidelity (pct d r n k R tau (tensorPower n rho)) (tensorPower (n+k) rho) := by sorry

end MixedCloning.Optimal
