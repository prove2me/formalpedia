-- Prove2me | Theorems.Thm_GibbsTransition_SizeCopies_system_size_copy_separation
-- name    : GibbsTransition.SizeCopies.system_size_copy_separation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T21:56:20.797236+00:00
-- url     : https://prove2.me/theorems/168b4ced-5a3f-49c1-8e64-6b431e20213b
-- title:
--   Theorem 3.1 — System size and number of copies
-- statement:
--   For every rational $0<\varepsilon\le1/16$, set $\beta=512/\varepsilon$ and $\delta=1/10$. Every correct learner on the entire class $\mathcal C^*$ whose side lengths are almost surely at most $\lfloor\kappa/\varepsilon\rfloor$ satisfies
--
--   $$\sup_{u\in\mathcal C^*}\mathbb E_u[N]\ge\frac45\exp(52/\varepsilon).$$
--
--   The lower bound permits arbitrary measurable instruments, retained quantum memory, collective measurements and unbounded almost-sure stopping, with infinite expectations included.
--
--   There are absolute positive constants $C_{\rm size}>\kappa$, $C_N,C_V,C_T$, a natural degree $p$ and a single finite local-measurement program, fixed before $\varepsilon$ and $u$, that is correct at the same temperature and confidence and satisfies jointly
--
--   $$L_{\max}\le\lceil C_{\rm size}/\varepsilon\rceil,\qquad
--   N\le C_N\log^2(1/\varepsilon),\qquad V\le C_V\varepsilon^{-3},\qquad
--   \mathbb E_u[T]\le C_T B_{\rm acc}^p.$$
--
--   Here $N$ counts fresh cubes, $V$ counts every supplied spin, and $T$ is the charged bit-operation cost of actual finite code. All quantum measurements of the upper learner are single-site $\{P,I-P\}$ measurements. This is both halves of Theorem 3.1, including all resources, locality and classical processing; no commutativity restriction is made on the unknown interaction.
--
--   The program must realize the source search law, with its exact interval updates, side lengths and rationally selected sample counts. The implementation requirement holds for all admissible interactions, without supplying their descriptions.
--
--   Differences from the source:
--   - encoding: fresh-state instruments, almost-sure stopping and expected costs → arbitrary-basis trace-class matrix kernels, CP event maps, induced finite-horizon laws and ENNReal limits; reason: complete positivity, Born consistency and trace preservation describe the same instruments; absorbing finite horizons recover stopped output laws and nonnegative costs, including infinity
--   - generalization: classically controlled algorithms → all measurable instance-independent classical policies and instruments, without an effectiveness requirement on the lower-bound adversary; reason: every source algorithm is such a policy; the same fresh-state hybrid estimate applies, and the full source claim is obtained by restriction
--   - encoding: a uniform local-measurement learner with polynomial expected classical processing → one finite binary-stack program with fair-coin and fresh single-site P-measurement instructions, and charged execution; reason: rational arithmetic, rejection sampling, logarithm approximations and interval control are effective bit algorithms; the interpreter supplies their Born law and counts actual operations rather than a supplied runtime annotation
--   - encoding: O size, copy and spin bounds → positive absolute constants quantified before inputs and unknown interactions, with deterministic bounds at every finite horizon; reason: the source schedule has fixed sample counts and geometric volumes, so its bounds hold on every execution; almost-sure stopping gives the same final bounds and their expectations
-- source:
--   Yuhao Cai, Zhenzhang Li, STOC 2027 submission #1168 (October 2026), Theorem 3.1 and proof, printed p. 5 (PDF p. 7); §2.2, printed p. 4 (PDF p. 6); §8, printed p. 18 (PDF p. 20); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1168.pdf

import Mathlib
import Definitions.Def_GibbsTransition_SizeCopies_LocalProgram

set_option autoImplicit false

open scoped ENNReal

namespace GibbsTransition.SizeCopies

/-- Theorem 3.1 in full: unrestricted operational lower bound and a uniform
finite-program local upper learner with size, copies, spins and bit time.
Suprema and expectations live in ENNReal, including infinite costs. -/
theorem system_size_copy_separation :
    (∀ (epsilon : ℚ), 0 < epsilon → epsilon ≤ 1/16 →
      ∀ (O ι : Type) [MeasurableSpace O] (A : Experiment O ι),
        IsExperiment A → LearnsClass A (512/epsilon) epsilon (1/10) →
        (∀ u, InClass u →
          experimentCap A u (512/epsilon) ⌊kappa / (epsilon : ℝ)⌋₊) →
        ENNReal.ofReal ((4/5 : ℝ) * Real.exp (52/(epsilon : ℝ))) ≤
          ⨆ u : {u : Interaction // InClass u}, experimentCopies A u.val (512/epsilon)) ∧
    (∃ (Csize Ccopies Cspins Ctime : ℝ) (degree : ℕ) (P : LocalProgram),
      kappa < Csize ∧ 0 < Ccopies ∧ 0 < Cspins ∧ 0 < Ctime ∧ ImplementsUpper P ∧
      ∀ (epsilon : ℚ), 0 < epsilon → epsilon ≤ 1/16 → ∀ u, InClass u →
        programCorrect P u (512/epsilon) epsilon (1/10) ∧
        programResources P u (512/epsilon) epsilon (1/10) ⌈Csize / (epsilon : ℝ)⌉₊
          (Ccopies * (Real.log (1/(epsilon : ℝ)))^2)
          (Cspins * (epsilon : ℝ)⁻¹^3) ∧
        polynomialTimeAt P u (512/epsilon) epsilon (1/10) Ctime degree) := by sorry

end GibbsTransition.SizeCopies
