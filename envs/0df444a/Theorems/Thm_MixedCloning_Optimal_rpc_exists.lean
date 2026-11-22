-- Prove2me | Theorems.Thm_MixedCloning_Optimal_rpc_exists
-- name    : MixedCloning.Optimal.rpc_exists
-- status  : Open
-- author  : @dmitry
-- created : 2026-11-22T01:21:09.311332+00:00
-- url     : https://prove2.me/theorems/c5656f6a-5ef1-42f7-80f1-c77dbccd4b25
-- title:
--   Section 2.3 — existence of the random purification channel $\mathrm{RPC}^{(d,r,n)}$
-- statement:
--   Fix integers $d\ge1$, $1\le r\le d$ and $n\ge0$. Let $A_1,\dots,A_n$ be copies of $\mathbb C^d$ and $B_1,\dots,B_n$ copies of $\mathbb C^r$. There exists a quantum channel (a linear, completely positive, trace-preserving map, given by a normalized Kraus family)
--
--   $$
--   \mathrm{RPC}^{(d,r,n)}:\ \mathrm{L}\big((\mathbb C^d)^{\otimes n}\big)\to\mathrm{L}\big((\mathbb C^d\otimes\mathbb C^r)^{\otimes n}\big)
--   $$
--
--   with the following property. For every state $\rho$ on $\mathbb C^d$ of rank at most $r$, and every unit vector $|\rho_0\rangle\in\mathbb C^d\otimes\mathbb C^r$ with $\operatorname{tr}_B|\rho_0\rangle\langle\rho_0|=\rho$,
--
--   $$
--   \mathrm{RPC}^{(d,r,n)}\big(\rho^{\otimes n}\big)=\int_{\mathrm U(r)}\Big((I\otimes U)\,|\rho_0\rangle\langle\rho_0|\,(I\otimes U^\dagger)\Big)^{\otimes n}\,dU,
--   $$
--
--   where $dU$ is the normalized Haar measure on the unitary group $\mathrm U(r)$.
--
--   This is the random purification channel of Tang, Wright and Zhandry, as stated in Section 2.3 of the source. It maps $n$ copies of a mixed state of rank at most $r$ to $n$ copies of a consistent but Haar-random purification on $\mathbb C^d\otimes\mathbb C^r$. It is the first stage of the purify–clone–trace (PCT) cloner and is exactly the second clause of Theorem 1.
--
--   **Formalization Note** The specification is the platform predicate `IsRPC d r n R`. The displayed identity is required for every purification $|\rho_0\rangle$ in $\mathbb C^d\otimes\mathbb C^r$, not just for one fixed choice, matching the source, where $|\rho_0\rangle$ may be any fixed purification of $\rho$. Tensor registers are ordered as $(A_1B_1)\cdots(A_nB_n)$, and the case $n=0$ is included, where the empty tensor power is one-dimensional.
--
--   Differences from the source:
--   - restriction: any $r\ge1$ → $1\le r\le d$; reason: matches the parameter range of Theorem 1, whose second clause this statement is; Section 2.3 itself imposes no upper bound on $r$
--   - generalization: $n\ge1$ copies → every $n\ge0$; reason: for $n=0$ both sides are the trivial one-dimensional state, matching clause 2 of Theorem 1
--   - encoding: the action for one fixed purification $|\rho_0\rangle$ → the same identity for every unit purification in $\mathbb C^d\otimes\mathbb C^r$; reason: the source allows any fixed purification, so the channel must satisfy the identity for each choice
-- source:
--   Dmitry Grinko, Marco Fanizza, Thilo Scharnhorst, Jack Spilecki, Optimal cloning of mixed states, STOC 2027 submission #243 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/243.pdf, p. 12, Section 2.3 (existence of RPC(d,r,n), attributed to [TWZ25] E. Tang, J. Wright, M. Zhandry, Conjugate queries can help, 2025); this is clause 2 of Theorem 1 (p. 4).

import Definitions.Def_MixedCloning_Optimal_Model

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace MixedCloning.Optimal
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Section 2.3 (PDF p.12), citing Tang–Wright–Zhandry [TWZ25]: for every number of
copies `n` there is a random purification channel `RPC^{(d,r,n)}`, i.e. a channel whose
action on every `ρ^{⊗n}` with `rank ρ ≤ r` is the Haar average of `n` copies of a random
purification of `ρ` in `ℂ^d ⊗ ℂ^r` (the specification `IsRPC`). -/
theorem rpc_exists (d r n : ℕ) (hd : 1 ≤ d) (hr : 1 ≤ r) (hrd : r ≤ d) :
    ∃ R : QAlgorithms.Superop (Word (Fin d) n) (Word (Fin d × Fin r) n), IsRPC d r n R := by sorry

end MixedCloning.Optimal
