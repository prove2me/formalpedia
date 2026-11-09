-- Prove2me | Theorems.Thm_LindbladTolerant_Testing_time_upper_bound
-- name    : LindbladTolerant.Testing.time_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:16:36.371825+00:00
-- url     : https://prove2.me/theorems/8be85178-d4fd-4ed0-9c65-949548eefea7
-- title:
--   Theorem 5.1 — Time upper bound
-- statement:
--   Fix $k\ge1$ and $n\ge1$, a strength bound $\Lambda>0$, and thresholds $0\le\varepsilon_1<\varepsilon_2\le\Lambda/\sqrt2$. Put $\Delta=\varepsilon_2-\varepsilon_1$. The unknown time-independent generator has diamond norm at most $\Lambda$ and admits a representation by traceless jumps, each supported on one set of at most $k$ qubits. The Hamiltonian and jump coefficients and supports are unknown; overlap and the number of jumps are unrestricted. Success means probability at least $2/3$ on both promise cases, with any answer allowed in the strict gap.
--
--   There is one admissible tester for each known parameter tuple, independent of the unknown generator, that solves the promise problem uniformly over the whole class. Its $M$-query admissible realization has the output law of the explicitly defined physical Algorithm 1, which uses duration $t=T/M$ per attempt. Storage is sufficient on every intermediate branch, and its pathwise time bound is
--   $$T=\frac{32q_k^2\lceil C_k\delta^{-2}\rceil}{\varepsilon_2}\le A_k\frac{\varepsilon_2}{\Delta^2},\qquad
--   \delta=\frac{\Delta}{32\varepsilon_2},\quad A_k=32768q_k^2(C_k+1).$$
--   Here $q_k=\sqrt{1+(2^k+1)/2}$ and $C_k$ is the explicit constant fixed by the proof of Theorem 4.3. Both depend only on $k$ and are chosen before $n,\Lambda$ and the thresholds. The call count is $M=\lceil\max\{1,2\Lambda T,32\Lambda^2T^2\}\rceil$. Every attempt, successful or failed, costs $t$.
--
--   **Formalization Note** Eqs.(99)–(105) bound ideal failure by $1/32+1/100$ and Eq.(109) adds at most $1/32$ for the physical experiment. Thus the probability guarantee applies to the actual forward oracle. Realization, storage sufficiency, and success are conclusions; ideal jump copies or a successful tester are not assumed.
--
--   Differences from the source:
--   - encoding: linear operators on the n-qubit Hilbert space → matrices in the fixed bit-string computational basis; reason: the basis representation and normalized matrix-unit formulas preserve every source instance
--   - encoding: O_k(eps2/Delta^2) total time → the physical Algorithm 1 with exact batches, pathwise total T, and A_k = 32768 q_k^2(C_k+1); reason: the source proof and the ceiling-derived copy bound supply these uniform constants and this implementation
--   - encoding: the Section 3 adaptive forward-evolution tester with free known operations and measurements → a bounded-query circuit of measurable completely positive instrument densities, varying finite quantum memory, and nested Born lintegrals; reason: scalar domination represents finite-dimensional instruments; zero-duration padding represents initial randomness and stopping, and disjoint-register channels sequentialize parallel calls while preserving summed pathwise time
-- source:
--   Jinge Bao, Yiyi Cai, Zhong-Xia Shang, Optimal Tolerant Testing of Lindbladian Dissipation, STOC 2027 submission #238 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/238.pdf, Theorem 5.1, p.26, PDF p.26; Algorithm 1 and proof pp.26–28, PDF pp.26–28, Eqs.(96)–(110)

import Definitions.Def_LindbladTolerant_Testing_algorithm

set_option autoImplicit false
open scoped ComplexOrder

namespace LindbladTolerant.Testing

theorem time_upper_bound : UniformUpper := by sorry

end LindbladTolerant.Testing
