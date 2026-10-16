-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_upper_at_scale
-- name    : OAI.ShortEgyptian.upper_at_scale
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:55:37.504988+00:00
-- url     : https://prove2.me/theorems/b78d78b3-502d-48a3-a455-73bb1964585c
-- title:
--   Egyptian expansions of $a/b$ with $O(\log S)$ terms for $b=e^S$, assuming dense numerator data
-- statement:
--   An **expansion** of a fraction $a/b$ is a strictly increasing list $n_1<n_2<\dots<n_\ell$ of natural numbers with every $n_i\ge 2$ and $\sum_{i=1}^{\ell}1/n_i=a/b$ in $\mathbb{Q}$; $\ell$ is its length. Fix the integer constants $D_M=2002\cdot102$, $D_X=D_M+2$, $D_C=4D_X$ and the real constants
--   $$
--   K_{\mathrm{gr}}=\frac{D_C}{(\log 2)^2}+\frac1{\log 2}+2,\qquad K_{\mathrm{den}}=\frac{100000}{\log 2}+\frac{1}{\log(10000/9999)}+3+30000\,D_X,\qquad K_{\mathrm{up}}=K_{\mathrm{gr}}+2K_{\mathrm{den}} .
--   $$
--
--   For a real number $S$ and a natural number $C$, a **dense datum at scale $S$ for $C$** consists of a natural number $M$ and a finite set $G$ of natural numbers such that
--
--   1. $e^S<M\le e^{D_M S}$;
--   2. $G\subseteq\{1,2,\dots,\lfloor e^{D_X S}\rfloor\}$, and at most $e^{D_X S}/8$ elements of $\{1,2,\dots,\lfloor e^{D_X S}\rfloor\}$ are not in $G$;
--   3. for every $u\in G$, the fraction $u/(MC)$ is a sum of at most $K_{\mathrm{den}}\log S$ unit fractions $1/m$ with $m\ge 2$ (repetitions allowed).
--
--   **Theorem.** Let $S$ be a real number with $S\ge 2$ and $\log S\ge 1$, and assume that a dense datum at scale $S$ exists for every natural number $C$ with $e^{D_C S}\le C\le e^{2D_C S}$. Then for all natural numbers $a,b$ with $0<a<b$ and $b=e^S$, the fraction $a/b$ has an expansion $n_1<\dots<n_\ell$ with
--
--   $$
--   \ell\le K_{\mathrm{up}}\log S .
--   $$
--
--   Since $b=e^S$ means $S=\log b$, this is the upper bound $O(\log\log b)$ for the shortest expansion of every $a/b$, conditional on the existence of dense data at scale $S=\log b$; that existence is established separately for all sufficiently large $S$. The theorem is the assembly step of the upper bound: greedy preparation, then a two-term splitting of the remainder, then removal of repeated denominators.
--
--   **Formalization Note** Dense data form the Lean structure `DenseData S C` (with fields `M`, `G` and the three properties), so the hypothesis is stated with `Nonempty`. The constants are `dimM`, `dimX`, `dimC`, `greedyConstant`, `densityConstant` ($=K_{\mathrm{den}}$) and `upperConstant`; the condition $b=e^S$ is an equality between the real cast of $b$ and `Real.exp S`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/UpperAssembly.lean#L58-L111

import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ParameterBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FourierDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowSpectrum
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_EmpiricalDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorWeights
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TruncatedDivisors
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SmoothBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorMoments
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeLists
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeProducts
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_HammingDistance
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SamplePartitions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ProductCorrelations
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ListSelection
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_LevelSelection
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ListConstruction
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ScaleGeometry
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ScaleBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ResidueSystem
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TerminalScale
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DescentSets
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_MomentRecurrence
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Density
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_GreedyPreparation
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_UpperAssembly

open OAI OAI.ShortEgyptian
attribute [local instance] scaleFinDecidableEq
open scoped BigOperators
open Finset Classical Filter Topology

theorem OAI.ShortEgyptian.upper_at_scale (S : ℝ) (hS : 2≤S) (hlog : 1≤Real.log S)
    (hdens : ∀ C : ℕ, Real.exp ((dimC:ℝ)*S)≤C → (C:ℝ)≤Real.exp (2*(dimC:ℝ)*S) → Nonempty (DenseData S C))
    (a b : ℕ) (ha : 0<a) (hab : a<b) (hb : (b:ℝ)=Real.exp S) :
    ∃ ns, IsExpansion a b ns ∧ (ns.length:ℝ)≤upperConstant*Real.log S := by sorry
