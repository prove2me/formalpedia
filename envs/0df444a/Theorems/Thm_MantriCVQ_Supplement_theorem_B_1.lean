-- Prove2me | Theorems.Thm_MantriCVQ_Supplement_theorem_B_1
-- name    : MantriCVQ.Supplement.theorem_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:12:01.943738+00:00
-- url     : https://prove2.me/theorems/928b316a-a775-4e5e-8d9c-73dde4e3ef19
-- title:
--   Theorem B.1 — a DNF of width less than $P(n,h)$ on the leaves changes its expectation by at most $2^{-2\sqrt n}$ between the root values
-- statement:
--   Fix the degree $d$ of the code family. There is a threshold on $n$, depending only on $d$, beyond which the following holds for every $h\le h_{\max}(n)$. Every DNF $\Phi$ on the leaves of an instance of size $n$ and height $h$ with width less than $P(n,h)$ satisfies
--   $$\big|\mathbb E\,\Phi(X^1)-\mathbb E\,\Phi(X^0)\big|\le 2^{-2\sqrt n},$$
--   where $(X^0,X^1)$ is the coupled pair of leaf tables with root values $0$ and $1$ of Section 4.2 and $P(n,h)=\prod_{i<h}(\lfloor m_i/(16d)\rfloor+1)$.
--
--   Unlike the switching lemmas of Section 6, the bound is uniform over all heights up to $h_{\max}(n)$. It is the width lower bound behind the message lower bound of Theorem B.4.
--
--   **Formalization Note** The threshold is chosen before the code family, which enters only through its degree. $\mathbb E\,\Phi(X^b)$ is the probability that $\Phi(X^b)=1$ under the uniform seed of the random projections; width counts literals in the list form of $\Phi$.
--
--   Differences from the source:
--   - encoding: E Φ(X^b) for the coupled pair (X^0, X^1) → Pr over the uniform Seed of Φ.eval(gen C s b) = true; reason: the coupled pair of §4.2 is gen from one uniform seed, as in the base Theorem 1.7
--   - encoding: a DNF of width less than P(n, h) (after normalization) → a SamplingAC0.DNF list with listWidth < Pthr d n h; reason: the conclusion depends only on the Boolean function; every DNF of normalized width W has a list form of width W
--   - encoding: a code family of degree d; a threshold depending only on d → ∃ n₀ before ∀ C : CodeDeg d; reason: Appendix B uses the code family only through its degree
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), Theorem B.1, p. 48 (PDF p. 50); t_i and P(n, h), p. 47 (PDF p. 49)

import Mathlib
import Definitions.Def_MantriCVQ_Supplement_Pthr
import Definitions.Def_MantriCVQ_CodeDeg
import Definitions.Def_MantriCVQ_Pr
import Definitions.Def_MantriCVQ_Seed
import Definitions.Def_MantriCVQ_dimsRange
import Definitions.Def_MantriCVQ_listWidth
import Definitions.Def_SamplingAC0_DNF

open QAlgorithms.Complexity

namespace MantriCVQ.Supplement

open MantriCVQ

/-- **Theorem B.1** (Width reduction to a constant; Mantri, arXiv:2610.37635 (PDF sha256
d1fab777…1d0b33), Theorem B.1, p. 48 (PDF p. 50); `t_i`, `P(n, h)` on p. 47 (PDF p. 49)): there is a
threshold on `n`, depending only on `d`, beyond which the following holds for every `h ≤ h_max(n)`.
Every DNF `Φ` on the leaves of an instance of size `n` and height `h` with width less than `P(n, h)`
satisfies `|E Φ(X¹) − E Φ(X⁰)| ≤ 2^{−2√n}`.

**Formalization Note** The code family enters only through its degree `d` (`CodeDeg d`), and the
threshold `n₀` is chosen before the code family. `(X⁰, X¹)` is the coupled pair `gen` from one uniform
seed (§4.2), as in `MantriCVQ.theorem_1_7`, and `E Φ(X^b)` is the probability that `Φ(X^b) = 1`. The
width is `listWidth` (repeated literals counted each time); the conclusion depends only on the Boolean
function of `Φ`, and every DNF of width `W` in the paper's normalized sense has a list form of width
`W` computing the same function, so the statement covers every DNF of the paper. `h = 0` is included
(`P(n, 0) = 1`). -/
theorem theorem_B_1 (d : ℕ) :
    ∃ n₀ : ℕ, ∀ C : CodeDeg d, ∀ n h : ℕ, n₀ ≤ n → h ≤ hmax n →
      ∀ Φ : SamplingAC0.DNF (Addr (dimsRange n 0 h)), listWidth Φ < Pthr d n h →
        |Pr (fun s : Seed (dimsRange n 0 h) => Φ.eval (gen C.code _ s true) = true) -
            Pr (fun s : Seed (dimsRange n 0 h) => Φ.eval (gen C.code _ s false) = true)| ≤
          (2 : ℝ) ^ (-(2 * Real.sqrt n)) := by sorry

end MantriCVQ.Supplement
