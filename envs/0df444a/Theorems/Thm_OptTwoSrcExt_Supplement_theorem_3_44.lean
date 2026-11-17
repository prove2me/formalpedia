-- Prove2me | Theorems.Thm_OptTwoSrcExt_Supplement_theorem_3_44
-- name    : OptTwoSrcExt.Supplement.theorem_3_44
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:39:36.754624+00:00
-- url     : https://prove2.me/theorems/bb6206ba-6912-409d-afa1-e130408018c4
-- title:
--   Theorem 3.44 — amortized recognition for arbitrary maps via the Gold defect
-- statement:
--   Let $L=\mathbb F_{2^N}$, let $A\subseteq L$ have size $2^{N-a}$ and let $f:A\to L$ be arbitrary. Let $r=d_c(f;A)$ be the Gold defect (3.45). If $p\ge1$ and $c\ge4p-1$ are integers and $N>2c$, then
--   $$2^{-3N}E\big(\mathrm{Graph}(f|_A)\big)\ge2^{-32a-32r/p-128p}.\tag{3.46}$$
--   Consequently, for an absolute constant $R_*$ independent of $p,c,N,A,f$, there are an $\mathbb F_2$-affine map $\ell:L\to L$ and a set $A_1\subseteq A$ on which $f=\ell$, with
--   $$|A_1|\ge2^{N-R_*(a+r/p+p+1)}.\tag{3.47}$$
--   The affine map may be singular, and there is no condition on the fibers or the image size of $f$. Here $E(S)$ is the number of quadruples in $S^4$ with zero sum.
--
--   The theorem converts a small Gold defect into large graph energy and then into agreement with an affine map on a large set, which is how the rank-margin arguments recognize near-affine tamperings.
--
--   **Formalization Note** $L$ is Mathlib's `GaloisField 2 N`; the binary identification $L\cong\mathbb F_2^N$ enters only through $\mathrm{RM}(2,N)$ and affine maps, which do not depend on the chosen basis. $f$ is a map $L\to L$ of which only the values on $A$ matter. $a$ is real. $R_*>0$ is chosen first.
--
--   Differences from the source:
--   - encoding: f : A → L arbitrary; ℓ : L → L affine → f : L → L (only its values on A enter); ℓ an 𝔽₂-affine map GaloisField 2 N →ᵃ GaloisField 2 N; reason: every map on A extends to L; affine maps between binary-coordinate representations are 𝔽₂-affine by the paper's convention (p.13)
-- source:
--   X. Li, Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate, STOC 2027 submission (manuscript sha256 2edb00b2…), Theorem 3.44, p.56 (PDF p.58); definitions pp.53–55 (PDF pp.55–57)

import Mathlib
import Definitions.Def_OptTwoSrcExt_Supplement_goldDefect

namespace OptTwoSrcExt.Supplement

/-- **Theorem 3.44 (Amortized recognition for arbitrary maps).**
Li, *Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate*, STOC 2027
submission (manuscript sha256 2edb00b2…), Theorem 3.44, printed p.56 (PDF p.58): "Let A ⊆ L have
size 2^{N−a} and let f : A → L be arbitrary. Let r = dc(f; A) be the Gold defect in (3.45). If
p ⩾ 1, c ⩾ 4p − 1, and N > 2c, then 2^{−3N} E(Graph(f|A)) ⩾ 2^{−32a−32r/p−128p}. (3.46)
Consequently, for an absolute constant R∗ independent of p, c, N, A, f, there is an affine map
ℓ : L → L and a set A1 ⊆ A on which f = ℓ, with |A1| ⩾ 2^{N−R∗(a+r/p+p+1)}. (3.47) The affine map
may be singular. There is no condition on the fibers or the image size of f."

There is an absolute `R∗ > 0` such that, for `L = 𝔽_{2^N}`, every `A ⊆ L` with `|A| = 2^{N−a}`
(`a` real), every map `f` (only its values on `A` matter) and all integers `p ≥ 1`, `c ≥ 4p − 1`
with `N > 2c`, writing `r = d_c(f; A)` for the Gold defect (3.45):
1. `2^{−3N} E(Graph(f|_A)) ≥ 2^{−32a − 32r/p − 128p}`, where `E(S)` counts the quadruples of `S⁴`
   with zero sum (`Graph(f|_A) = {(x, f(x)) : x ∈ A} ⊆ L × L`);
2. there are an `𝔽₂`-affine map `ℓ : L → L` (possibly singular) and `A₁ ⊆ A` with `f = ℓ` on `A₁`
   and `|A₁| ≥ 2^{N − R∗(a + r/p + p + 1)}`.

**Formalization Note.** `L` is Mathlib's `GaloisField 2 N`; the binary identification `L ≅ 𝔽₂^N`
enters only through `RM(2, N)` and affine maps, which do not depend on the chosen `𝔽₂`-basis. `f` is
a map `L → L`; every `f : A → L` is the restriction of one. `R∗` is chosen before `N, p, c, A, f`.
Logarithms are base 2. -/
theorem theorem_3_44 :
    ∃ Rs : ℝ, 0 < Rs ∧ ∀ (N p c : ℕ), 1 ≤ p → 4 * p - 1 ≤ c → 2 * c < N →
      ∀ (A : Finset (GaloisField 2 N)) (a : ℝ), (A.card : ℝ) = (2 : ℝ) ^ ((N : ℝ) - a) →
      ∀ f : GaloisField 2 N → GaloisField 2 N,
        (2 : ℝ) ^ (-(3 * (N : ℝ))) * (addEnergy (graphOn A f) : ℝ) ≥
            (2 : ℝ) ^ (-32 * a - 32 * (goldDefect c A f : ℝ) / p - 128 * p) ∧
          ∃ (ℓ : GaloisField 2 N →ᵃ[ZMod 2] GaloisField 2 N) (A₁ : Finset (GaloisField 2 N)),
            A₁ ⊆ A ∧ (∀ x ∈ A₁, f x = ℓ x) ∧
            (A₁.card : ℝ) ≥ (2 : ℝ) ^ ((N : ℝ) - Rs * (a + (goldDefect c A f : ℝ) / p + p + 1)) := by sorry

end OptTwoSrcExt.Supplement
