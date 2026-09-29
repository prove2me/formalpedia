-- Prove2me | Theorems.Thm_ModularCurve_jCoordinate_spec_modularFunctionFieldBar
-- name    : ModularCurve.jCoordinate_spec_modularFunctionFieldBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/408383eb-30ec-5fbd-ae5b-f0942d44a202
-- title:
--   Values of the j-coordinate at places of X₀(N)
-- statement:
--   Let $N$ be a non-zero natural number. Let $\bar{\jmath}$ denote the element of the intermediate field $\overline{\mathbb{Q}} \subseteq$ `modularFunctionFieldBar N` $\subseteq \overline{\mathbb{Q}}((q))$ obtained by applying `coeffEmb` (coefficientwise application of $\mathbb{Q} \to \overline{\mathbb{Q}}$ to a Laurent series) to `jq` $= q^{-1} \cdot$ `jNumQ`, the $q$-expansion of the modular invariant $j$; here `modularFunctionFieldBar N` is the field generated over $\overline{\mathbb{Q}}$ inside $\overline{\mathbb{Q}}((q))$ by the `coeffEmb`-images of `modularFunctionFieldFull N` $= \mathbb{Q}(\mathrm{divisorExpansions}\ N)$, and the membership of $\bar{\jmath}$ is supplied by `coeffEmb_mem_laurentBaseChange` applied to `jq_mem_full N`. Places here are the structures `Place` $\overline{\mathbb{Q}}$ (`modularFunctionFieldBar N`): valuation subrings containing the constants $\overline{\mathbb{Q}}$, proper, and principal ideal rings; `ord` is the associated $\mathbb{Z}$-valued order function. The conclusion is the conjunction of three assertions: (1) for every such place $v$ with $v.\mathrm{ord}\,\bar{\jmath} \ge 0$ there is exactly one constant $c \in \overline{\mathbb{Q}}$ with $v.\mathrm{ord}(\bar{\jmath} - c) > 0$; (2) for every $c \in \overline{\mathbb{Q}}$ the set of places $v$ with $v.\mathrm{ord}(\bar{\jmath} - c) > 0$ is finite; (3) the set of places $v$ with $v.\mathrm{ord}\,\bar{\jmath} < 0$ is finite.
--
--   This is the statement that the $j$-coordinate defines a finite map from the places of the geometric function field of $X_0(N)$ to $\mathbb{P}^1$ over $\overline{\mathbb{Q}}$: every place at which $\bar{\jmath}$ is regular has a well-defined value in $\overline{\mathbb{Q}}$ (so residue fields are $\overline{\mathbb{Q}}$), fibres over constants are finite, and the poles, i.e. the cusps, are finitely many. It is used in the comparison of the naive logarithmic height of the $j$-coordinate with the height attached to places, and in the Northcott property for that height.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_jCoordinate_spec_modularFunctionFieldBar.lean

import Definitions.Def_ModularCurve_AtkinLehner

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.jCoordinate_spec_modularFunctionFieldBar (N : ℕ) [NeZero N] :
    (∀ (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
        0 ≤ v.ord ⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (L := AlgebraicClosure ℚ) (hx := jq_mem_full N)⟩ →
        ∃! c : AlgebraicClosure ℚ,
          0 < v.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (L := AlgebraicClosure ℚ) (hx := jq_mem_full N)⟩ -
            algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c)) ∧
      (∀ c : AlgebraicClosure ℚ,
        {v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) |
          0 < v.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (L := AlgebraicClosure ℚ) (hx := jq_mem_full N)⟩ -
            algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c)}.Finite) ∧
      ({v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) |
        v.ord ⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (L := AlgebraicClosure ℚ) (hx := jq_mem_full N)⟩ < 0}.Finite) := by sorry
