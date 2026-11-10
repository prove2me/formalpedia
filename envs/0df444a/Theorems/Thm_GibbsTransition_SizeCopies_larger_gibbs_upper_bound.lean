-- Prove2me | Theorems.Thm_GibbsTransition_SizeCopies_larger_gibbs_upper_bound
-- name    : GibbsTransition.SizeCopies.larger_gibbs_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T21:55:33.507725+00:00
-- url     : https://prove2.me/theorems/810e0429-2811-4cc9-a3e3-85b4530a1575
-- title:
--   Theorem 5.1 — Learning from larger Gibbs states
-- statement:
--   There are fixed positive absolute constants $C_{\rm size}>\kappa$, $C_N,C_V,C_T$, a natural degree $p$ and one finite local-measurement program such that the following holds simultaneously for all rational $0<\varepsilon\le1/16$, $0<\delta\le1/4$, $\beta\ge256/(d\varepsilon)=512/\varepsilon$, and every $u\in\mathcal C^*$. The same program is $(\varepsilon,\delta)$ correct, terminates almost surely, and has
--
--   $$L_{\max}\le\lceil C_{\rm size}/\varepsilon\rceil,\qquad
--   N\le C_N[K\log(1/\delta)+K^2],\qquad
--   V\le C_V\varepsilon^{-3}\log(1/\delta),$$
--
--   where $K=\lceil\log(1/(4\varepsilon))/\log(8/5)\rceil$. Its expected classical processing is at most $C_T B_{\rm acc}^p$, where $B_{\rm acc}$ is the exact binary length of the accuracy and confidence inputs. Quantum instructions measure only the public $P$ at one site of a fresh cube. Input arithmetic, random bits, oracle arguments and output reading are charged by the interpreter.
--
--   All constants and code precede accuracy, confidence, temperature and the unknown interaction. This includes the processing assertion in the source proof and §8. The source schedule permits $C_{\rm size}=865$; the quantified constants retain its exact rates.
--
--   The program must realize the source search law, with its exact interval updates, side lengths and rationally selected sample counts. The implementation requirement holds for all admissible interactions, without supplying their descriptions.
--
--   Differences from the source:
--   - encoding: a uniform local-measurement learner with polynomial expected classical processing → one finite binary-stack program with fair-coin and fresh single-site P-measurement instructions, and charged execution; reason: rational arithmetic, rejection sampling, logarithm approximations and interval control are effective bit algorithms; the interpreter supplies their Born law and counts actual operations rather than a supplied runtime annotation
--   - encoding: O size, copy and spin bounds → positive absolute constants quantified before inputs and unknown interactions, with deterministic bounds at every finite horizon; reason: the source schedule has fixed sample counts and geometric volumes, so its bounds hold on every execution; almost-sure stopping gives the same final bounds and their expectations
-- source:
--   Yuhao Cai, Zhenzhang Li, STOC 2027 submission #1168 (October 2026), Theorem 5.1, Equation (27) and its proof, printed p. 9 (PDF p. 11); §8, printed p. 18 (PDF p. 20); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1168.pdf

import Mathlib
import Definitions.Def_GibbsTransition_SizeCopies_LocalProgram

set_option autoImplicit false

namespace GibbsTransition.SizeCopies

/-- Theorem 5.1, including the processing assertion in its proof and Section 8.
One finite program and all constants precede every input and unknown model.
Here d=1/2, so 256/(d epsilon)=512/epsilon. -/
theorem larger_gibbs_upper_bound :
    ∃ (Csize Ccopies Cspins Ctime : ℝ) (degree : ℕ) (P : LocalProgram),
      kappa < Csize ∧ 0 < Ccopies ∧ 0 < Cspins ∧ 0 < Ctime ∧ ImplementsUpper P ∧
      ∀ (epsilon delta beta : ℚ),
        0 < epsilon → epsilon ≤ 1/16 → 0 < delta → delta ≤ 1/4 →
        512/epsilon ≤ beta → ∀ u, InClass u →
        programCorrect P u beta epsilon delta ∧
        programResources P u beta epsilon delta ⌈Csize / (epsilon : ℝ)⌉₊
          (Ccopies * ((searchRounds epsilon : ℝ) * Real.log (1/(delta : ℝ)) +
            (searchRounds epsilon : ℝ)^2))
          (Cspins * (epsilon : ℝ)⁻¹^3 * Real.log (1/(delta : ℝ))) ∧
        polynomialTimeAt P u beta epsilon delta Ctime degree := by sorry

end GibbsTransition.SizeCopies
