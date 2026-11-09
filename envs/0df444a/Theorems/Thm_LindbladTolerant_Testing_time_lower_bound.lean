-- Prove2me | Theorems.Thm_LindbladTolerant_Testing_time_lower_bound
-- name    : LindbladTolerant.Testing.time_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:12:33.406984+00:00
-- url     : https://prove2.me/theorems/cb436f1f-d831-46ba-bed3-63cc7ea52391
-- title:
--   Theorem 5.2 — Time lower bound
-- statement:
--   Fix $k\ge1$ and $n\ge1$, a strength bound $\Lambda>0$, and thresholds $0\le\varepsilon_1<\varepsilon_2\le\Lambda/\sqrt2$. Put $\Delta=\varepsilon_2-\varepsilon_1$. The unknown time-independent generator has diamond norm at most $\Lambda$ and admits a representation by traceless jumps, each supported on one set of at most $k$ qubits. The Hamiltonian and jump coefficients and supports are unknown; overlap and the number of jumps are unrestricted. Success means probability at least $2/3$ on both promise cases, with any answer allowed in the strict gap.
--
--   Every admissible tester that succeeds uniformly over this entire class and has pathwise total time at most $T$ satisfies the source-derived bound
--   $$T\ge\sqrt2\log(9/8)\frac{(\sqrt{\varepsilon_2}+\sqrt{\varepsilon_1})^2}{\Delta^2}\ge c\frac{\varepsilon_2}{\Delta^2},\qquad c=\sqrt2\log(9/8)>0.$$
--   The quantifier includes adaptive real durations, arbitrary measurable classical outcomes and randomness, arbitrary ancillary dimensions and retained quantum memory, and joint measurements. Cost is the sum of all durations on every branch, including parallel calls.
--
--   This is a lower bound for solving the full class, rather than for one chosen measurement or a restricted family of testers.
--
--   **Formalization Note** The constant is Eq.(119), p.30. The hard family in its proof is $\mathcal L_\Gamma(X)=\Gamma(Z_1XZ_1-X)$, with norms $\sqrt2\Gamma$ and $2\Gamma$. Rates $\varepsilon_1/\sqrt2$ and $\varepsilon_2/\sqrt2$ give the exact boundary instances, including zero lower rate. No Poisson simulation or data-processing bound is a premise of the formal statement.
--
--   Differences from the source:
--   - encoding: linear operators on the n-qubit Hilbert space → matrices in the fixed bit-string computational basis; reason: the basis representation and normalized matrix-unit formulas preserve every source instance
--   - encoding: Omega(eps2/Delta^2) total time → Eq.(119) and its consequence with c = sqrt(2) log(9/8); reason: the proof establishes the displayed universal coefficient, including eps1 = 0
--   - encoding: the Section 3 adaptive forward-evolution tester with free known operations and measurements → a bounded-query circuit of measurable completely positive instrument densities, varying finite quantum memory, and nested Born lintegrals; reason: scalar domination represents finite-dimensional instruments; zero-duration padding represents initial randomness and stopping, and disjoint-register channels sequentialize parallel calls while preserving summed pathwise time
-- source:
--   Jinge Bao, Yiyi Cai, Zhong-Xia Shang, Optimal Tolerant Testing of Lindbladian Dissipation, STOC 2027 submission #238 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/238.pdf, Theorem 5.2, p.28, PDF p.28; proof pp.28–30, PDF pp.28–30, Eqs.(111)–(119)

import Definitions.Def_LindbladTolerant_Testing_algorithm

set_option autoImplicit false
open scoped ComplexOrder

namespace LindbladTolerant.Testing

theorem time_lower_bound : UniformLower := by sorry

end LindbladTolerant.Testing
