-- Prove2me | Theorems.Thm_OAI_Erdos3_allocated_weighted_physical_replacement_s2
-- name    : OAI.Erdos3.allocated_weighted_physical_replacement_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:49:55.463558+00:00
-- url     : https://prove2.me/theorems/783404ef-b4d1-4722-85f2-73249bc88868
-- title:
--   Weighted averages of the physical box residual along parameter progressions of smooth affine samples are small
-- statement:
--   Let $J$ and $I$ be finite types with decidable equality, with $|J|$ and $|I|$ elements, and let $k_0 \in J$. Let $D, r, Q$ be natural numbers, $\mathrm{anchor}, \mathrm{parLo}, \mathrm{parHi} : J \to \mathbb{Z}$ with $\mathrm{parLo}_j < \mathrm{parHi}_j$ for all $j$, $H : I \to \mathbb{R}$, and $L, C, \kappa, A, \epsilon$ real numbers with $1 \le L$, $1 \le C$, $0 < \kappa$, $0 \le A$, $0 < \epsilon$. Assume, for every $j \in J$,
--   $$\Bigl|\frac{\mathrm{anchor}_j + D\,\mathrm{parLo}_j}{L}\Bigr| \le C, \qquad \Bigl|\frac{\mathrm{anchor}_j + D\,\mathrm{parHi}_j}{L}\Bigr| \le C,$$
--   and $\kappa L \le D\,(r+1)$. Let $\mathrm{origin} : \mathrm{Option}\,J \times I \to \mathbb{Z}$, $\mathrm{lo} : I \to \mathbb{Z}$, $N : I \to \mathbb{N}$, and natural numbers $\mathrm{degree}$ and $\mathrm{exponent} \ge 2$. Let $f : \mathbb{Z}^{I} \to \mathbb{R}$ with $0 \le f(x) \le 1$ for every $x$ in the translated box $\mathrm{Box} = \{x : \mathrm{lo}_i \le x_i < \mathrm{lo}_i + N_i \ \forall i\}$ (OpenAI's `translatedIntegerBox lo N`). Let $\mathrm{modLog}, \mathrm{dimLog}$ be real numbers with $0 \le \mathrm{modLog}$, $Q \le e^{\mathrm{modLog}}$ and $|I| \le e^{\mathrm{dimLog}}$. Assume for every $i \in I$: $H_i \le 2N_i$, $N_i \le A\,H_i$, and
--   $$\texttt{physicalReplacementScaleThreshold}\ |I|\ k_0\ Q\ C\ \kappa\ A\ \epsilon\ \mathrm{degree}\ \mathrm{modLog}\ \mathrm{dimLog} \cdot L^{\mathrm{exponent}} \le H_i,$$
--   where `physicalReplacementScaleThreshold` is an explicit real quantity defined by OpenAI. Assume further $Q \le 2^{\mathrm{degree}}$. Let $B, R$ be natural numbers with $D B \le Q$ and $0 < B$, assume $2 \le |J|$, and let $\mathrm{parMin} > 0$ be a real number with $\mathrm{parMin} \le \mathrm{parHi}_j - \mathrm{parLo}_j \le R$ for every $j$. Let $W$ be a finite set of functions $z : \mathrm{Option}\,J \times I \to \mathbb{Z}$ such that for every $z \in W$ and every index $(c, i)$,
--   $$|z(c,i) - \mathrm{origin}(c,i)| \le \tfrac12\,\texttt{smoothPairCoefficientScale}\ (H_i)\ L\ c,$$
--   where `smoothPairCoefficientScale H L c` (OpenAI) is $H$ if $c = \mathrm{none}$ and $H/L$ if $c \in J$. Let $v : (\mathrm{Option}\,J \times I \to \mathbb{Z}) \to \mathbb{R}$ with $0 \le v(z) \le 1$ for all $z$.
--
--   Put $\rho$ = `physicalPairGridAccuracy |I| k₀ C κ A ε` (an explicit real quantity of OpenAI). The hypotheses imply (by OpenAI's lemma `physicalReplacementScaleThreshold_conditions`) that $4 \le \rho H_i$ and $\rho H_i \le 2 N_i$ for every $i$; with these proofs, let $P$ = `normalizedBoxPartitions N H ρ …`, the family (indexed by $i$) of partitions of $\{0, \dots, N_i - 1\}$ into consecutive intervals of length $\lfloor \rho H_i / 2 \rfloor$, except that the last interval also absorbs the remainder (all parts have positive length). For $x \in \mathbb{Z}^{I}$, `physicalBoxResidual lo N P hpos (boundedPrimePower Q) degree f x` (OpenAI) is $0$ if $x \notin \mathrm{Box}$, and otherwise $f(x)$ minus a truncation of $f$ at $x$: on the product cell of the partitions containing $x$ (translated by $\mathrm{lo}$), take the density of the residues of a uniform point of the cell modulo the moduli $p^{\lfloor \log_p Q \rfloor}$ for the primes $p \le Q$ (relative to the uniform distribution on those residues), and evaluate at the residues of $x$ the sum of its ANOVA components over the sets of at most $\mathrm{degree}$ primes. For $t \in \prod_j [\mathrm{parLo}_j, \mathrm{parHi}_j)$ and $z$ as above, `smoothAffineSample (fun j => anchor j + D t_j) z` is the point $i \mapsto z(\mathrm{none}, i) + \sum_{j \in J} (\mathrm{anchor}_j + D t_j)\, z(j, i)$ of $\mathbb{Z}^I$ (OpenAI).
--
--   Then
--   $$\Bigl|\,\mathbb{E}_{z \in W}\, v(z)\, \mathbb{E}_{t}\, \texttt{physicalBoxResidual}\ \mathrm{lo}\ N\ P\ \mathrm{hpos}\ (\texttt{boundedPrimePower}\ Q)\ \mathrm{degree}\ f\ \bigl(\texttt{smoothAffineSample}\ (\mathrm{anchor} + D t)\ z\bigr)\Bigr|$$
--   $$\le \frac{3^{(|J|+1)|I|}\,\prod_{(c,i)} \texttt{smoothPairCoefficientScale}\ (H_i)\ L\ c}{|W|}\cdot \sqrt{2^{|I|+1} A^{|I|}\,\texttt{integerBoxBadPairBudget}\ |J|\ B\ R\ r\ \mathrm{parMin} + \epsilon},$$
--   where $t$ is uniform on $\prod_{j} [\mathrm{parLo}_j, \mathrm{parHi}_j) \cap \mathbb{Z}$, the product runs over $\mathrm{Option}\,J \times I$, and `integerBoxBadPairBudget d B R r L` $= 2^{d-1}\bigl(B^{-(d-1)} + R/L^{d}\bigr) + \bigl((2r+1)/L\bigr)^{d}$ (OpenAI).
--
--   Lean: `OAI.Erdos3.allocated_weighted_physical_replacement_s2`, which states OpenAI's `OAI.Erdos3.allocated_weighted_physical_replacement` (in `lean/OAI/Combinatorics/Progressions/Estimates/SmallWeightedPhysicalReplacement.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B218` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/SmallWeightedPhysicalReplacement.lean (declaration OAI.Erdos3.allocated_weighted_physical_replacement)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B218

section

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem allocated_weighted_physical_replacement_s2 {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (k0 : J) (D r : ℕ) (anchor parLo parHi : J → ℤ) (hpar : ∀ j, parLo j < parHi j)
    (H : I → ℝ) {L C κ A epsilon : ℝ} (Q : ℕ)
    (hL : 1 ≤ L) (hC : 1 ≤ C) (hκ : 0 < κ) (hA : 0 ≤ A) (heps : 0 < epsilon)
    (hleft : ∀ j, |((anchor j + (D : ℤ) * parLo j : ℤ) : ℝ) / L| ≤ C)
    (hright : ∀ j, |((anchor j + (D : ℤ) * parHi j : ℤ) : ℝ) / L| ≤ C)
    (hgap : κ * L ≤ (D : ℝ) * (r + 1 : ℕ))
    (origin : Option J × I → ℤ) (lo : I → ℤ) (N : I → ℕ)
    (degree exponent : ℕ) (hexponent : 2 ≤ exponent)
    (f : (I → ℤ) → ℝ) (hf : ∀ x ∈ translatedIntegerBox lo N, 0 ≤ f x ∧ f x ≤ 1)
    (modLog dimLog : ℝ) (hmodLog : 0 ≤ modLog)
    (hQlog : (Q : ℝ) ≤ Real.exp modLog) (hdim : (Fintype.card I : ℝ) ≤ Real.exp dimLog)
    (hupper : ∀ i, H i ≤ 2 * (N i : ℝ)) (hratio : ∀ i, (N i : ℝ) ≤ A * H i)
    (hsize : ∀ i, physicalReplacementScaleThreshold (Fintype.card I) k0 Q C κ A epsilon degree modLog dimLog *
      L ^ exponent ≤ H i)
    (hQdegree : Q ≤ 2 ^ degree)
    (B R : ℕ) (hBQ : D * B ≤ Q) (hB : 0 < B) (hparamDim : 2 ≤ Fintype.card J)
    (parMin : ℝ) (hparMin : 0 < parMin)
    (hparSide : ∀ j, parMin ≤ ((parHi j - parLo j : ℤ) : ℝ))
    (hparWidth : ∀ j, parHi j - parLo j ≤ (R : ℤ))
    (W : Finset (Option J × I → ℤ))
    (hW : ∀ z ∈ W, ∀ i, |(z i : ℝ) - (origin i : ℝ)| ≤ smoothPairCoefficientScale (H i.2) L i.1 / 2)
    (v : (Option J × I → ℤ) → ℝ) (hv : ∀ z, 0 ≤ v z ∧ v z ≤ 1) :
    let rho := physicalPairGridAccuracy (Fintype.card I) k0 C κ A epsilon
    let sc := fun i => physicalReplacementScaleThreshold_conditions (Fintype.card I) k0 Q C κ degree modLog dimLog
      (zero_le_one.trans hC) hA heps hL hexponent (hsize i) (hupper i)
    let hlarge := fun i => (sc i).2.2.1
    let hwhole := fun i => (sc i).2.2.2.2.2.2
    let P := normalizedBoxPartitions N H rho hlarge hwhole
    let hpos := normalizedBoxPartitions_positive N H rho hlarge hwhole
    |𝔼 z ∈ W, v z * (𝔼 t : (∀ j, Finset.Ico (parLo j) (parHi j)),
      physicalBoxResidual lo N P hpos (boundedPrimePower Q) degree f
        (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) z))| ≤
      ((3 : ℝ) ^ Fintype.card (Option J × I) *
        (∏ z : Option J × I, smoothPairCoefficientScale (H z.2) L z.1) / W.card) *
      Real.sqrt ((2 : ℝ) ^ (Fintype.card I + 1) * A ^ Fintype.card I *
        integerBoxBadPairBudget (Fintype.card J) B R r parMin + epsilon) := by
  sorry

end Erdos3

end

end OAI
end
