-- Prove2me | Theorems.Thm_OAI_Erdos3_RationalFilteredNilmanifold_exists_prescribed_square_image_partition_s2
-- name    : OAI.Erdos3.RationalFilteredNilmanifold.exists_prescribed_square_image_partition_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T11:43:05.769568+00:00
-- url     : https://prove2.me/theorems/a20ef10f-12fc-47c3-9ec6-bea0d48c913d
-- title:
--   The prescribed square-image partition specification holds for some exponent C
-- statement:
--   For all natural numbers $s, t, k_0, a$ there is a natural number $C \ge 2$ such that `PrescribedSquareImagePartitionSpec s t k₀ a C` holds. That is OpenAI's predicate (a long proposition, not unfolded here) quantifying over rational filtered nilmanifolds $D$ (degree $s$, on a $\mathbb{Q}$-Lie algebra $L$ in `Type`), $V$ (degree $s$, on the square subalgebra of $D$'s filtration) and $Q$ (degree $t$, on a $\mathbb{Q}$-Lie algebra $M$ in `Type`), a $\mathbb{Q}$-Lie homomorphism $\varphi$ from the square subalgebra to $M$, a polynomial orbit $g$ of $D$, an integer $c$, positive naturals $q, N$, and reals $p \ge 2$ and $0 < \varepsilon \le 1$, under hypotheses $1 \le s$, geometry complexity at most $p$ for $D$, $V$, $Q$, log-height bounds $p$ on the coordinates of the square-pair map and of $\varphi$ on $V$'s basis, $q \le e^p$ and $1/\varepsilon \le \exp((p+2)^a)$. Its conclusion provides $0 < \delta \le \varepsilon$ with $1/\delta \le \exp((p+C)^C)$ and a partition of unity $(A_j)$ on $\mathbb{Z}/N$, indexed by $(\mathrm{Fin}\ n \times \mathbb{Z}/q) \times \mathrm{Fin}\ k$ with at most $\exp((p+C)^C)$ indices, in which each $A_j$ is a `PositiveCyclicNiltest` of degree $s$ and complexity $(p+C)^C$, is supported on the residue class $j_{1,2}$ mod $q$ and on a set of circle-diameter at most $\delta$, together with a bound $6\delta + 3/N$ on the density of the exceptional set `cyclicWrapExceptional h δ`, and an $\varepsilon$-closeness statement in $Q$'s metric for the images under $\varphi$ of a square-filtration orbit $r_{\mathrm{Sq}}$ at points $x, y$ (outside the exceptional set, with $A_i(x)A_j(x+h) > 0$ and $A_i(y)A_j(y+h) > 0$), for every shift $h$, branch in $\mathrm{Fin}\ 2$, $\eta, \gamma$ in the real group with $\gamma$ in the real lattice and the coordinates of $\eta$ at most $\exp((p+2)^{k_0})$, and every $r_{\mathrm{Sq}}$ whose two projections are the translates of $g$ prescribed in the predicate.
--
--   Lean: `OAI.Erdos3.RationalFilteredNilmanifold.exists_prescribed_square_image_partition_s2`, which states OpenAI's `OAI.Erdos3.RationalFilteredNilmanifold.exists_prescribed_square_image_partition` (in `lean/OAI/Combinatorics/Progressions/Estimates/PrescribedSquareImagePartition.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B175` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/PrescribedSquareImagePartition.lean (declaration OAI.Erdos3.RationalFilteredNilmanifold.exists_prescribed_square_image_partition)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B175

section

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_prescribed_square_image_partition_s2 (s t k₀ a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ PrescribedSquareImagePartitionSpec s t k₀ a C := by
  sorry

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end
