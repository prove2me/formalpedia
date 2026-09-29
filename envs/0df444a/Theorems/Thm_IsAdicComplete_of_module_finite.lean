-- Prove2me | Theorems.Thm_IsAdicComplete_of_module_finite
-- name    : IsAdicComplete.of_module_finite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/8ddeff09-4f80-58f8-a173-05fe3d11453d
-- title:
--   Finite modules over a complete Noetherian ring are adically complete
-- statement:
--   Let $R$ be a commutative Noetherian ring, let $I \subseteq R$ be an ideal, and assume $R$ is $I$-adically complete, that is, $I$-adically Hausdorff ($\bigcap_n I^n = 0$) and $I$-adically precomplete (every sequence $(x_n)$ in $R$ with $x_m \equiv x_n \bmod I^m$ for all $m \le n$ has a limit, i.e. some $L$ with $L \equiv x_n \bmod I^n$ for all $n$). Let $M$ be an $R$-module which is finite over $R$, i.e. finitely generated. Then $M$ is $I$-adically complete in the same sense for modules: the intersection of the submodules $I^n \cdot M$ is zero, and for every sequence $(x_n)$ in $M$ satisfying $x_m - x_n \in I^m \cdot M$ whenever $m \le n$ there exists $L \in M$ with $L - x_n \in I^n \cdot M$ for all $n$. No hypothesis of local-ness, of $I$ being proper, or of separatedness of $M$ beyond what follows from the above is imposed; the module $M$ may live in a universe different from that of $R$.
--
--   This is the standard fact that adic completeness is inherited by finitely generated modules over a complete Noetherian ring, the module-theoretic complement of the Krull intersection theorem. It is used in the project whenever one works adically over a complete Noetherian local ring $\mathcal{O}$ — for instance for Hecke algebras and other $\mathcal{O}$-algebras that are finite as $\mathcal{O}$-modules, and for comparing completions along base change and along localisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsAdicComplete_of_module_finite.lean

import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.AdicCompletion.Noetherian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

theorem IsAdicComplete.of_module_finite {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R] (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] : IsAdicComplete I M := by sorry
