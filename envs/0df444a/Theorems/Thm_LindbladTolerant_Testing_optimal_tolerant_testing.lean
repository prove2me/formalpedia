-- Prove2me | Theorems.Thm_LindbladTolerant_Testing_optimal_tolerant_testing
-- name    : LindbladTolerant.Testing.optimal_tolerant_testing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:18:18.237371+00:00
-- url     : https://prove2.me/theorems/6f381bd3-bab8-483c-a7eb-ae56e6a3beba
-- title:
--   Theorem 1.1 — Optimal tolerant dissipation testing
-- statement:
--   Fix $k\ge1$ and $n\ge1$, a strength bound $\Lambda>0$, and thresholds $0\le\varepsilon_1<\varepsilon_2\le\Lambda/\sqrt2$. Put $\Delta=\varepsilon_2-\varepsilon_1$. The unknown time-independent generator has diamond norm at most $\Lambda$ and admits a representation by traceless jumps, each supported on one set of at most $k$ qubits. The Hamiltonian and jump coefficients and supports are unknown; overlap and the number of jumps are unrestricted. Success means probability at least $2/3$ on both promise cases, with any answer allowed in the strict gap.
--
--   The optimal summed forward-evolution time is
--   $$\Theta_k\!\left(\frac{\varepsilon_2}{(\varepsilon_2-\varepsilon_1)^2}\right).$$
--   Precisely, both uniform resource contracts hold. First, the explicitly defined physical Algorithm 1 is realized by one admissible tester for each known parameter tuple, succeeds uniformly on the source class, and spends at most $A_k\varepsilon_2/\Delta^2$ on every branch, where $A_k=32768q_k^2(C_k+1)>0$. Second, every admissible uniformly successful tester with a pathwise time bound $T$ obeys
--   $$T\ge c\frac{(\sqrt{\varepsilon_2}+\sqrt{\varepsilon_1})^2}{\Delta^2}\ge c\frac{\varepsilon_2}{\Delta^2},\qquad c=\sqrt2\log(9/8)>0.$$
--   Here $q_k=\sqrt{1+(2^k+1)/2}$ and $C_k$ is the ceiling-derived copy-estimator constant. These coefficients are fixed before $n,\Lambda$ and the thresholds. The complete upper contract retains the exact batch counts, stored-copy sufficiency, and physical Born output law. The complete lower contract allows adaptive protocols, measurable classical outcomes, arbitrary ancillary systems, retained outputs, and joint measurements.
--
--   This combines Theorems 5.1 and 5.2 as one goal. It measures interaction time, without asserting that an optimum over all protocols is attained.
--
--   **Formalization Note** The domain includes $k>n$, $\varepsilon_1=0$, and $\varepsilon_2=\Lambda/\sqrt2$. Canonical data are computed from the generator; they are not inputs available to the tester. No rate–state identity, physical/ideal comparison, estimator success, or lower-bound simulation is a hypothesis.
--
--   Differences from the source:
--   - encoding: linear operators on the n-qubit Hilbert space → matrices in the fixed bit-string computational basis; reason: the basis representation and normalized matrix-unit formulas preserve every source instance
--   - encoding: the two-sided Theta_k time bound → the conjunction of both full uniform resource contracts with explicit proof-derived constants; reason: the two inequalities express asymptotic optimality without a possibly unattained real infimum
--   - encoding: the Section 3 adaptive forward-evolution tester with free known operations and measurements → a bounded-query circuit of measurable completely positive instrument densities, varying finite quantum memory, and nested Born lintegrals; reason: scalar domination represents finite-dimensional instruments; zero-duration padding represents initial randomness and stopping, and disjoint-register channels sequentialize parallel calls while preserving summed pathwise time
-- source:
--   Jinge Bao, Yiyi Cai, Zhong-Xia Shang, Optimal Tolerant Testing of Lindbladian Dissipation, STOC 2027 submission #238 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/238.pdf, Theorem 1.1, p.4, PDF p.4; full formal components Theorems 5.1 and 5.2, pp.26,28, PDF pp.26,28, proofs through p.30

import Definitions.Def_LindbladTolerant_Testing_algorithm

set_option autoImplicit false
open scoped ComplexOrder

namespace LindbladTolerant.Testing

theorem optimal_tolerant_testing : UniformUpper ∧ UniformLower := by sorry

end LindbladTolerant.Testing
