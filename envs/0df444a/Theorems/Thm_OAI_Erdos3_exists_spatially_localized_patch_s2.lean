-- Prove2me | Theorems.Thm_OAI_Erdos3_exists_spatially_localized_patch_s2
-- name    : OAI.Erdos3.exists_spatially_localized_patch_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:29:37.392469+00:00
-- url     : https://prove2.me/theorems/05f9fe44-c4a6-430e-9bbf-427086bb4d6c
-- title:
--   A score against a recovered-lift patch sum yields a polynomial patch with positive score on a residue box slice
-- statement:
--   Let $\iota, \sigma$ be types with $\iota$ finite with decidable equality. Let $N : \iota \to \mathbb{N}$ with $N_i > 0$ for all $i$, and $q_0 > 0$ a natural number. Let $s, d, E, m$ be natural numbers and $w : \mathrm{Fin}\ d \to \mathbb{N}$ monotone with $1 \le w_j \le s$ for all $j$. Let $P_j$ ($j \in \mathrm{Fin}\ d$) be real polynomials in the variables $\sigma$ of total degree at most $w_j$ (membership in `weightedSupportLE (fun _ => 1) (w j)`). Let $p : \mathrm{Fin}\ m \to \mathbb{N}$ and let $B$ be a `WeightedParameterPatch (σ ⊕ Fin m) (Sum.elim (fun _ => 1) p) s E` (defined by OpenAI: weighted polynomial slots in the variables $\sigma \oplus \mathrm{Fin}\ m$, where the variables in $\sigma$ have weight $1$ and the variable $i \in \mathrm{Fin}\ m$ has weight $p_i$, together with a patch kernel with Lipschitz constant `B.kernel.lip`; `B.value` is a real function). Let $\chi$ be a `PatchKernel m` (defined by OpenAI: a $[0,1]$-valued function on $\mathbb{R}^m$ supported in $\{|x_i| \le 1/4 \ \forall i\}$ and Lipschitz with constant `χ.lip`). Let $M : \mathrm{Fin}\ m \to \mathrm{Fin}\ d \to \mathbb{Z}$ and $K \in \mathbb{R}_{\ge 0}$ with $\sum_j |M_{ij}| \le K$ for all $i$ and $w_j \le p_i$ whenever $M_{ij} \ne 0$.
--
--   Let $G : (\iota \to \mathbb{R}) \to (\iota \to \mathbb{Z}/q_0) \to (\mathrm{Fin}\ m \to \mathbb{Z}) \to (\mathrm{Fin}\ m \to \mathbb{R}) \to \mathbb{R}$ and $\Lambda, L, C \in \mathbb{R}_{\ge 0}$ with $C \ge 1$, such that: for all $r, b, y$ the map $z \mapsto G(z, r, b, y)$ is $\Lambda$-Lipschitz; for all $z, r, b$ the map $G(z, r, b, \cdot)$ is $L$-Lipschitz; $G(z, r, b, y) \in [0, C]$ always; and $G(z, r, c + Mk, \cdot) = G(z, r, c, \cdot)$ for all $z, r$, $c \in \mathbb{Z}^m$ and $k \in \mathbb{Z}^d$ (`recoveredIntegerLift M c k` $= c + Mk$).
--
--   Let $q$ be a natural number with $q \ge 8$ and $16K \le q$. Let $t$ assign to each point $u \in \prod_i \mathrm{Fin}(N_i)$ a point $t(u) \in \mathbb{R}^\sigma$, and let $\mathrm{score} : \prod_i \mathrm{Fin}(N_i) \to \mathbb{R}$. Let $\tau, \rho, \theta, S$ be real numbers with $\tau \ge 0$, $0 < \rho \le 1$, $\theta > 0$, $|\mathrm{score}(u)| \le 1$ for all $u$, $2q_0 \le \rho N_i$ for all $i$,
--   $$S \le \mathbb{E}_{u}\ \mathrm{score}(u)\cdot \sum_{b \in \mathbb{Z}^m} \chi(y_{u,b})\cdot G\bigl(\bar u, (u_i \bmod q_0)_i, b, y_{u,b}\bigr)\cdot \texttt{B.value}\bigl(t(u), b\bigr),$$
--   where the expectation is uniform over $u \in \prod_i \mathrm{Fin}(N_i)$, the sum over $b$ is an unconditional sum (`tsum`), $y_{u,b} = M\cdot(P_j(t(u)))_j - b \in \mathbb{R}^m$, $\bar u = (u_i/N_i)_i$, and `B.value (t(u), b)` means `B.value` evaluated at the point equal to $t(u)$ on $\sigma$ and to $b$ on $\mathrm{Fin}\ m$; and suppose $\tau + \Lambda\rho + C\theta < S$.
--
--   Then there exist a `ResidueBoxSlice N q₀` $A$ (defined by OpenAI: a start $a_i$ and length $\ell_i$ for each $i$ such that $a_i + q_0 j < N_i$ for all $j < \ell_i$; its points are $(a_i + q_0 j_i)_i$) and a `PolynomialPatch σ s (d + E)` $Q$ such that:
--   - $\theta\rho N_i / (4 q_0 (|\iota| + 1)) \le \ell_i$ and $0 < \ell_i$ for every $i$;
--   - `Q.kernel.lip` $\le q\,(2q^{d} + 1) + (\texttt{χ.lip} + L/C)\,K + \texttt{B.kernel.lip}$;
--   - $$\frac{\tau}{C q^{d}} \le \mathbb{E}_{j \in \prod_i \mathrm{Fin}(\ell_i)}\ \mathrm{score}(\texttt{A.point}\ j)\cdot \texttt{Q.value}\bigl(t(\texttt{A.point}\ j)\bigr).$$
--
--   Lean: `OAI.Erdos3.exists_spatially_localized_patch_s2`, which states OpenAI's `OAI.Erdos3.exists_spatially_localized_patch` (in `lean/OAI/Combinatorics/Progressions/Geometry/ActualFixedSpatialRetainedPatchEndpoint.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B037`, `OAIE3v2B069` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/ActualFixedSpatialRetainedPatchEndpoint.lean (declaration OAI.Erdos3.exists_spatially_localized_patch)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B037
import Definitions.Def_OAIE3v2B069

section

namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped NNReal BigOperators

theorem exists_spatially_localized_patch_s2 {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    (N : ι → ℕ) (hN : ∀ i, 0 < N i) (q₀ : ℕ) (hq₀ : 0 < q₀) {s d E m : ℕ}
    (w : Fin d → ℕ) (hw : ∀ j, 1 ≤ w j) (hws : ∀ j, w j ≤ s) (hmono : Monotone w)
    (P : Fin d → MvPolynomial σ ℝ) (hP : ∀ j, P j ∈ weightedSupportLE (fun _ : σ => 1) (w j))
    (p : Fin m → ℕ) (B : WeightedParameterPatch (σ ⊕ Fin m) (Sum.elim (fun _ => 1) p) s E)
    (χ : PatchKernel m) (M : Fin m → Fin d → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K) (hweight : ∀ i j, M i j ≠ 0 → w j ≤ p i)
    (G : (ι → ℝ) → (ι → ZMod q₀) → (Fin m → ℤ) → (Fin m → ℝ) → ℝ)
    (Λ L C : ℝ≥0) (hC : 1 ≤ C)
    (hGspace : ∀ r b y, LipschitzWith Λ (fun z => G z r b y))
    (hGlift : ∀ z r b, LipschitzWith L (G z r b))
    (hGcap : ∀ z r b y, G z r b y ∈ Set.Icc (0 : ℝ) C)
    (hinvariant : ∀ z r c k, G z r (recoveredIntegerLift M c k) = G z r c)
    (q : ℕ) (hq : 8 ≤ q) (hmesh : 16 * (K : ℝ) ≤ q)
    (t : (∀ i, Fin (N i)) → σ → ℝ) (score : (∀ i, Fin (N i)) → ℝ)
    {τ ρ θ S : ℝ} (hτ : 0 ≤ τ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hθ : 0 < θ)
    (hscoreBound : ∀ u, |score u| ≤ 1) (hlarge : ∀ i, 2 * (q₀ : ℝ) ≤ ρ * N i)
    (hscore : S ≤ 𝔼 u, score u * ∑' b : Fin m → ℤ,
      χ.value (fun i => realIntegerMatrix M (fun j => aeval (t u) (P j)) i - (b i : ℝ)) *
        G (BoxProgressionPartition.normalizedPoint u) (fun i => ((u i).val : ZMod q₀)) b
          (fun i => realIntegerMatrix M (fun j => aeval (t u) (P j)) i - (b i : ℝ)) *
        B.value (Sum.elim (t u) (fun i => (b i : ℝ))))
    (hbudget : τ + Λ * ρ + C * θ < S) :
    ∃ (A : ResidueBoxSlice N q₀) (Q : PolynomialPatch σ s (d + E)),
      (∀ i, θ * ρ * N i / (4 * q₀ * (Fintype.card ι + 1)) ≤ (A.length i : ℝ)) ∧
      (∀ i, 0 < A.length i) ∧
      Q.kernel.lip ≤ (q : ℝ≥0) * (2 * (q : ℝ≥0) ^ d + 1) +
        (χ.lip + L / C) * K + B.kernel.lip ∧
      τ / ((C : ℝ) * (q : ℝ) ^ d) ≤
        𝔼 j : (∀ i, Fin (A.length i)), score (A.point j) * Q.value (t (A.point j)) := by
  sorry

end Erdos3

end

end OAI
end
