-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocated_cover_site_expansion_s2
-- name    : OAI.Erdos3.VectorPolynomial.exists_allocated_cover_site_expansion_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T11:07:15.400004+00:00
-- url     : https://prove2.me/theorems/9336497e-ea1b-4b58-a50a-fa6bae377ebb
-- title:
--   A family of site expansions is a Lipschitz torus expansion on the lattice cover
-- statement:
--   Fix: a natural number $m$; a type $G$; finite types $I_j$ and natural numbers $n_j$ ($j \in \mathrm{Fin}\,m$); finite types $B_a$ over the axes $a$ of `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$); finite types $J_j$, real subspaces $U_j \subseteq \mathbb R^{J_j}$ and bases $b_j$ (indexed by $\mathrm{Fin}\,n_j$) of the orthogonal complements of `euclideanSubspace (U j)`; a real function $R$ on $\mathrm{Fin}\,m$; finite types $A$ and $S$; a family $e$ of `ScalarSiteExpansion`s on $S$ indexed by $A$ (each $e_a$ a finite family of terms $k$ with a period $p_k$, a coefficient in $\mathbb C$ and factors $\phi_{k,s} : \mathbb Z/p_k \times \mathbb R \to \mathbb C$ for $s \in S$); and a map $\mathrm{selected} : A \to \Sigma_j\, \mathrm{Fin}(n_j)$. Write $N_a =$ `allocatedPrincipalGridScale B U b j i` for $\mathrm{selected}(a) = \langle j, i\rangle$ (a natural number), and, for a choice $k = (k_a)_{a \in A}$ of terms, `commonSitePeriod e k` $= \prod_a p_{k_a}$.
--
--   Assume $R_j > 0$ for all $j$. Let $T, V, C, H : A \to \mathbb R$ and $L \in \mathbb R_{\ge 0}$ with `(e a).Bounds (T a) (V a) (C a) L (H a)` for all $a$ (at most $T_a$ terms, periods in $(0, V_a]$, coefficient norms summing to at most $C_a$, factors of norm at most $1$, $L$-Lipschitz in the real argument, vanishing for real arguments of absolute value at least $H_a$); let $Q \in \mathbb R_{\ge 0}$ with $8(|\texttt{layerIntegerPrincipalSlots B j i}| + 1) \le Q$ for $\langle j, i\rangle = \mathrm{selected}(a)$, for all $a$; let $o_j$ be orthonormal bases of `euclideanSubspace (U j)` indexed by $I_j$; let $C_{\mathrm{fwd}} : \mathrm{Fin}\,m \to \mathbb R_{\ge 0}$ with $\|\texttt{normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)}\,v\| \le C_{\mathrm{fwd},j}\|v\|$ for all $j, v$; let $K \in \mathbb R_{\ge 0}$ with $R_j^{-1} \le K$ for all $j$; assume (hb) the $\mathbb Z$-span of $b_j$ is `projectedIntegerLattice (euclideanSubspace (U j))` for all $j$; and let $E_j$ be finite types with $\mathbb Z$-bases $bW_j$ (indexed by $E_j$) of $\Lambda_j =$ `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))`.
--
--   Then there exists $g$, assigning to each term choice $k$ and each $s \in S$ a function $g_{k,s} : (\Sigma_j J_j \to \mathbb R/\mathbb Z) \to \mathbb C$, such that:
--
--   - each $g_{k,s}$ is Lipschitz with constant $\max\bigl(|A|\, L\, Q\, K \sum_j C_{\mathrm{fwd},j}|J_j| \cdot \texttt{commonSitePeriod e k},\ 4\cdot\texttt{commonSitePeriod e k}\bigr)$ and satisfies $\|g_{k,s}(v)\| \le 1$ for all $v$;
--   - $\sum_k \|\texttt{coverSiteCoefficient e k}\| \le 2^{|S|}\prod_a C_a$, where `coverSiteCoefficient e k` is $2^{|S|}$ times the product coefficient of the family at $k$; and
--   - for all $u : S \to \prod_j$ `euclideanSubspace (U j)` and $w : S \to \prod_j \mathbb R^{I_j} \times \mathbb Z^{\mathrm{Fin}(n_j)}$ such that, for all $s, j$, the class of $u_{s,j}$ modulo $\Lambda_j$ equals `normalizedLatticeQuotient (euclideanSubspace (U j)) (b j) (hb j) (orthonormalMixedChart (o j) (w s j))`, and every coordinate of `normalizedLatticePoint (euclideanSubspace (U j)) (b j) (orthonormalMixedChart (o j) (w s j))` has absolute value at most $1/4$, we have
--   $$\sum_k \texttt{coverSiteCoefficient e k}\prod_{s \in S} g_{k,s}\Bigl(\langle j, x\rangle \mapsto \frac{u_{s,j}(x)}{\texttt{commonSitePeriod e k}} \bmod 1\Bigr) = \texttt{siteFamilyEval}\ e\ \bigl((s,a) \mapsto (w_{s,j})_2(i)\bigr)\ \bigl((s,a) \mapsto (w_{s,j})_2(i)/N_a\bigr),$$
--   with $\langle j, i\rangle = \mathrm{selected}(a)$, where `siteFamilyEval e y x` $= \sum_k (\text{product coefficient at } k)\prod_s (\text{product over } a \text{ of the factors of } e_a \text{ at } (y_{s,a} \bmod p_{k_a}, x_{s,a}))$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_allocated_cover_site_expansion_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.exists_allocated_cover_site_expansion` (in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedIdealPhysicalCover.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B126`, `OAIE3v2B129` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedIdealPhysicalCover.lean (declaration OAI.Erdos3.VectorPolynomial.exists_allocated_cover_site_expansion)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B126
import Definitions.Def_OAIE3v2B129

section

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite

namespace VectorPolynomial

open Module Submodule

variable {m : ℕ} {G : Type*} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R : Fin m → ℝ} {A S : Type*} [Fintype A] [Fintype S]
variable (e : A → ScalarSiteExpansion S) (selected : A → Σ j : Fin m, Fin (n j))

local notation "scale" => (fun a : A => allocatedPrincipalGridScale (G := G) B U b (R := R)
  (Sigma.fst (selected a)) (Sigma.snd (selected a)))

theorem exists_allocated_cover_site_expansion_s2 (hR : ∀ j, 0 < R j)
    {T V C H : A → ℝ} {L : ℝ≥0}
    (he : ∀ a, (e a).Bounds (T a) (V a) (C a) L (H a))
    (Q : ℝ≥0) (hQ : ∀ a, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (selected a).1 (selected a).2) : ℝ) + 1) ≤ Q)
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    {E : Fin m → Type*} [∀ j, Fintype (E j)]
    (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))) :
    ∃ g : (∀ a, (e a).Term) → S → (((Σ j, J j) → UnitAddCircle) → ℂ),
      (∀ k s, LipschitzWith (max (((Fintype.card A * L) * Q) *
        (K * ∑ j, Cforward j * Fintype.card (J j)) * commonSitePeriod e k)
          (4 * commonSitePeriod e k)) (g k s) ∧ ∀ v, ‖g k s v‖ ≤ 1) ∧
      (∑ k, ‖coverSiteCoefficient e k‖) ≤ (2 : ℝ) ^ Fintype.card S * ∏ a, C a ∧
      ∀ (u : S → ∀ j, euclideanSubspace (U j)) (w : S → ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)),
        (∀ s j, (QuotientAddGroup.mk (u s j) : euclideanSubspace (U j) ⧸
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) =
          normalizedLatticeQuotient (euclideanSubspace (U j)) (b j) (hb j) (orthonormalMixedChart (o j) (w s j))) →
        (∀ s j i, |normalizedLatticePoint (euclideanSubspace (U j)) (b j) (orthonormalMixedChart (o j) (w s j)) i| ≤ 1 / 4) →
        (∑ k, coverSiteCoefficient e k * ∏ s,
          g k s (fun a => ((((u s a.1).val a.2) / commonSitePeriod e k : ℝ) : UnitAddCircle))) =
          siteFamilyEval e (fun s a => (w s (selected a).1).2 (selected a).2)
            (fun s a => ((w s (selected a).1).2 (selected a).2 : ℝ) / (scale) a) := by
  sorry

end VectorPolynomial
end Erdos3

end

end OAI
end
