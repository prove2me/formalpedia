-- Prove2me | Theorems.Thm_ModularCurve_exists_jZeroNeronAtPDataOrdV22_pNew
-- name    : ModularCurve.exists_jZeroNeronAtPDataOrdV22_pNew
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/9acf65eb-6240-5941-bd3e-9927e6f8c77d
-- title:
--   At-p Néron ordinary datum for J₀(N₀p) with p-new toric part
-- statement:
--   Let $N_0$ and $p$ be natural numbers with $N_0 \neq 0$ and $p$ a nonzero prime, assume $p \nmid N_0$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` lying over $p$ in the sense that $p$, viewed in $\overline{\mathbb{Q}}$, belongs to the nonunits of $A$. Then there exists a datum $\mathcal{D}$ of type `JZeroNeronAtPDataOrdV22 N₀ p hpN₀ A hA`, that is, a `JZeroNeronAtPDataOrdCore` for these inputs together with the additional guarded multiplicity bound: whenever $p \neq 2$, the predicates `HeckeInputsAll (N₀ * p)` and `HeckeOperatorsCommuteBar (N₀ * p)` hold, and $\mathfrak{m}$ is a maximal ideal of `HeckeAlg` $= \mathbb{Z}[x_\ell : \ell \text{ prime}]$ which is not eventually Eisenstein, contains $p$, has finite residue field and is such that the $\mathfrak{m}$-torsion $\mathrm{JZero}(N_0p)[\mathfrak{m}]$ (torsion by the set $\mathfrak{m}$, for the Hecke module structure `heckeModuleBar (N₀ * p)` on the degree-zero divisor class group of the modular function field of level $N_0p$ over $\overline{\mathbb{Q}}$) has dimension $2$ over `HeckeAlg ⧸ 𝔪`, then the cardinality of the intersection of the toric submodule at $p$ with this $\mathfrak{m}$-torsion is at most the cardinality of `HeckeAlg ⧸ 𝔪`; and such that three further properties hold. First, for every $m \in \mathbb{N}$ (including $m = 0$) every $x$ in $\mathcal{D}$'s toric part $\mathcal{D}.\mathrm{toric}\,m$ is annihilated by both components of `degeneracyPushforwardPair N₀ p`, the pair of homomorphisms $\mathrm{JZero}(N_0p) \to \mathrm{JZero}(N_0)$ given, when the degeneracy inputs hold, by the $\mathrm{Pic}^0$-push-forwards along the two degeneracy maps, and by $0$ otherwise. Second, there is $c > 0$ such that for every $m$ and every $x$ in the finite part $\mathcal{D}.\mathrm{fin}\,m$ annihilated by both push-forwards, $c \cdot x$ lies in $\mathcal{D}.\mathrm{toric}\,m$. Third, for every $m > 0$ the $m$-torsion subgroup of $\mathrm{JZero}(N_0p)$ has cardinality $m^{2\,\mathcal{D}.\mathrm{toricRank} + 2\,\mathcal{D}.\mathrm{abelianRank}}$.
--
--   This is the existence statement for the at-$p$ Néron ordinary datum of $J_0(N_0 p)$ in its version carrying the guarded toric multiplicity-one bound, packaging the local structure at $p$ of the Jacobian of the modular curve of level $N_0p$ (toric and finite parts, toric and abelian ranks) together with the $p$-new information that the toric part is killed by both degeneracy push-forwards to level $N_0$ and that the finite part is toric up to a bounded multiple. It is used by [`ModularCurve.hasJZeroNeronAtPDataOrdV22`](thm.html#ModularCurve.hasJZeroNeronAtPDataOrdV22), and through it in the level-lowering step at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_jZeroNeronAtPDataOrdV22_pNew.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronAtPDataOrdV22
import Definitions.Def_ModularCurve_ToricDescentData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.exists_jZeroNeronAtPDataOrdV22_pNew
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    ∃ 𝓓 : JZeroNeronAtPDataOrdV22 N₀ p hpN₀ A hA,
      (∀ (m : ℕ), ∀ x ∈ 𝓓.toric m,
      degeneracyPushforwardPair N₀ p 0 x = 0 ∧ degeneracyPushforwardPair N₀ p 1 x = 0) ∧
      (∃ c : ℕ, 0 < c ∧ ∀ (m : ℕ), ∀ x ∈ 𝓓.fin m,
      degeneracyPushforwardPair N₀ p 0 x = 0 → degeneracyPushforwardPair N₀ p 1 x = 0 →
        c • x ∈ 𝓓.toric m) ∧
      (∀ m : ℕ, 0 < m →
      Nat.card ↥(jZeroTorsion (N₀ * p) m) = m ^ (2 * 𝓓.toricRank + 2 * 𝓓.abelianRank)) := by sorry
