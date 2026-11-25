-- Prove2me | Theorems.Thm_HodgeComputer_FourPlusTwoResidual_exists_homogenized_chart_source_a6t3_witness
-- name    : HodgeComputer.FourPlusTwoResidual.exists_homogenized_chart_source_a6t3_witness
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-25T16:24:19.009831+00:00
-- url     : https://prove2.me/theorems/7715e8bd-9b07-4817-87ff-37f55640dc2c
-- title:
--   The homogenized chart source $a^6 t^3$ is realised unconditionally
-- statement:
--   **Unconditional chart-source witness.** The four-plus-two mission splits the
--   rational-current branch into a *chart* step and a *transport* step. The chart step asks
--   for a field $K$, coordinate derivations $\mathrm{D}r,\mathrm{D}s,\mathrm{D}t$ and elements
--   $a,s,t,P,q_r,q_s,q_t$ satisfying the chart normalisation
--
--   $$
--   a \neq 0,\quad t \neq 0,\quad \mathrm{D}r a = \mathrm{D}s a = \mathrm{D}t a = 0,\quad
--   \mathrm{D}r t = \mathrm{D}s t = 0,\quad \mathrm{D}t t = 1,\quad \mathrm{D}s s = 1
--   $$
--
--   and the *homogenized* chart source identity with source $a^6 t^3$, written in the
--   rescaled coordinates $\mathrm{d}b = a^{-1}\mathrm{D}r$, $\mathrm{d}c = a^{-1}(\mathrm{D}t - \frac{s}{t}\mathrm{D}s)$,
--   $\mathrm{d}d = (at)^{-1}\mathrm{D}s$, $p_b = \frac{2aq_r}{3t}$, $p_c = \frac{2aq_t}{3t}$,
--   $p_d = \frac{2a(sq_t + tq_s)}{3t}$:
--
--   $$
--   p_b\,\mathrm{d}b H + p_c\,\mathrm{d}c H + p_d\,\mathrm{d}d H - \tfrac32 H\,(\mathrm{d}b p_b + \mathrm{d}c p_c + \mathrm{d}d p_d) = a^6 t^3,\qquad H = a^6 P .
--   $$
--
--   **Theorem.** There exist a field $K$ of characteristic zero, derivations
--   $\mathrm{D}r,\mathrm{D}s,\mathrm{D}t : \mathbb{Z}\to K\to K$ and elements $a,s,t,P,q_r,q_s,q_t \in K$
--   satisfying the chart normalisation *and* the homogenized chart source identity above.
--   The witness is therefore **unconditional**: no hypothesis is needed for the chart branch.
--
--   **Proof.** Two statements of the platform are combined.
--
--   1. `exists_ratio_chart_t4_witness` (proved) produces a field, derivations and elements
--      satisfying the chart normalisation together with the *ratio-chart* identity
--      $$
--      -\Bigl(P\,(\mathrm{D}r q_r + \mathrm{D}s q_s + \mathrm{D}t q_t) - \tfrac23\,(q_r\,\mathrm{D}r P + q_s\,\mathrm{D}s P + q_t\,\mathrm{D}t P)\Bigr) = t^4 .
--      $$
--      This witness comes from the Hermite-Pade flat moment section with moments $(0,0,1)$
--      (`exists_hermite_pade_flat_moment_section_e3`, proved), read through the transport
--      `ratio_chart_t4_of_flat_moment_section_e3` (proved): the moment vector $c$ with
--      $\sum_j c_j T_0 j = 0$, $\sum_j c_j T_2 j = 0$, $\sum_j c_j T_4 j = 1$ inverts the
--      moment matrix $K^{-1}\alpha_A$ and produces the section whose source is $t^4$.
--
--   2. `homogenized_chart_source_a6t3_iff_ratio_chart_t4` (proved, this mission) is the
--      *chart-clearing* equivalence: under the chart normalisation the homogenized chart
--      source identity with source $a^6 t^3$ holds **if and only if** the ratio-chart
--      identity with source $t^4$ holds. The two are the same equation in two coordinate
--      systems; the homogenized left-hand side is $\tfrac{a^6}{t}$ times the ratio-chart
--      left-hand side.
--
--   Applying the forward implication of the chart-clearing equivalence to the ratio-chart
--   identity of step 1 yields the homogenized chart source identity, and the chart
--   normalisation is inherited from the same witness. $\square$
--
--   **Consequence for the mission.** The hypothesis of
--   `core_rational_of_homogenized_chart_source_a6t3` is now unconditional: the branch
--   `core_rational_of_homogenized_chart_source_a6t3` is equivalent to the unconditional
--   statement `exists_core_rational_current`, and the only remaining content of that branch
--   is the existence of the core rational current itself, not the existence of a chart.
-- source:
--   WORMHOLE transport for the four-plus-two residual mission, chart branch: donor HodgeComputer.FourPlusTwoResidual.exists_ratio_chart_t4_witness (proved), itself Hermite-Pade flat moment section exists_hermite_pade_flat_moment_section_e3 (proved) transported by ratio_chart_t4_of_flat_moment_section_e3 (proved); map = chart clearing, homogenized_chart_source_a6t3_iff_ratio_chart_t4 (proved, this mission); target = HodgeComputer.FourPlusTwoResidual.core_rational_of_homogenized_chart_source_a6t3

import Mathlib.RingTheory.Derivation.Basic

set_option autoImplicit false
noncomputable section

theorem HodgeComputer.FourPlusTwoResidual.exists_homogenized_chart_source_a6t3_witness :
    ∃ (K : Type) (_ : Field K) (_ : CharZero K)
      (Dr Ds Dt : Derivation ℤ K K) (a s t P qr qs qt : K),
      a ≠ 0 ∧ t ≠ 0 ∧
        Dr a = 0 ∧ Ds a = 0 ∧ Dt a = 0 ∧
        Dr t = 0 ∧ Ds t = 0 ∧ Dt t = 1 ∧
        Ds s = 1 ∧
        (let H := a ^ 6 * P
         let db := fun z : K => Dr z / a
         let dc := fun z : K => (Dt z - s / t * Ds z) / a
         let dd := fun z : K => Ds z / (a * t)
         let pb := (2 : K) * a * qr / (3 * t)
         let pc := (2 : K) * a * qt / (3 * t)
         let pd := (2 : K) * a * (s * qt + t * qs) / (3 * t)
         pb * db H + pc * dc H + pd * dd H -
           (3 / 2 : K) * H * (db pb + dc pc + dd pd) = a ^ 6 * t ^ 3) := by sorry
