-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_lemma_2_4
-- name    : InfoLossLAR.WorstCase.lemma_2_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:03:09.048197+00:00
-- url     : https://prove2.me/theorems/8bb20b76-164b-487e-a001-67fff234f3ae
-- title:
--   Lemma 2.4 — modular rank and image lattice of a rounding matrix
-- statement:
--   Let $q$ be an odd prime, $d\ge1$, and $T\in\mathbb Z^{d\times d}$ a rounding matrix of modular rank $r$, with unimodular $U,V$ such that $UTV=\operatorname{diag}(I_r,qI_\ell)$, $\ell=d-r$, and $P=E^\top U$ (the last $\ell$ rows of $U$). Then
--   $$\operatorname{rank}_{\mathbb F_q}(T\bmod q)=r,\qquad \dim_{\mathbb F_q}\ker(T\bmod q)=\ell,\qquad |\det T|=q^\ell,$$
--   $q\mathbb Z^d\subseteq\mathcal L(T)$, the map $z\mapsto Pz\bmod q$ from $\mathbb Z^d$ to $\mathbb F_q^\ell$ is onto with kernel exactly $\mathcal L(T)$ (so it induces $\mathbb Z^d/\mathcal L(T)\cong\mathbb F_q^\ell$), the quotient $\mathbb Z^d/\mathcal L(T)$ has $q^\ell$ elements, and it is nontrivial exactly when $\ell\ge1$.
--
--   The lemma identifies the output space of algebraic rounding: rounded outputs are read modulo $\mathcal L(T)$, a group of size $q^\ell$ with explicit coordinates.
--
--   Differences from the source:
--   - encoding: $\mathcal L(T)\subseteq\mathbb Z^d$ → holds by construction ($\mathcal L(T)$ is a $\mathbb Z$-submodule of $\mathbb Z^d$); reason: not a separate clause in Lean
--   - encoding: $\mathbb Z^d/\mathcal L(T)\cong\mathbb F_q^\ell$ via the last $\ell$ coordinates of $Uz$ mod $q$ → $z\mapsto Pz\bmod q$ is surjective with kernel $\mathcal L(T)$; reason: exactly the statement that the induced map is an isomorphism
--   - encoding: odd prime $q$, fixed Smith matrices, indices $1..d$ → `[Fact q.Prime]`, `q ≠ 2`, `SmithData q r d T`, `Fin d` and $\ell=d-r$; reason: Lean conventions, same instances
-- source:
--   Chen Qian, Information Loss Is All You Need: TC⁰ Pseudorandomness from Worst-Case Lattices, arXiv:2611.05136 (held version, sha256 2ebdfbf3…), p. 14, Lemma 2.4

import Mathlib
import Definitions.Def_InfoLossLAR_WorstCase_Rounding

set_option autoImplicit false

namespace InfoLossLAR.WorstCase

/-- Lemma 2.4 (Modular rank and image lattice), p. 14: for a rounding matrix `T` of modular rank
`r` with chosen Smith matrices `U, V` (`UTV = diag(I_r, qI_ℓ)`, `ℓ = d − r`, `q` an odd prime, `d ≥ 1`),
`rank_{𝔽_q}(T mod q) = r`, `dim ker(T mod q) = ℓ`, `|det T| = q^ℓ`, `qℤ^d ⊆ L(T)`, the map
`z ↦ (last ℓ coordinates of Uz) mod q` is onto `𝔽_q^ℓ` with kernel `L(T)` (so it induces
`ℤ^d/L(T) ≅ 𝔽_q^ℓ`), the quotient has `q^ℓ` elements, and it is nontrivial iff `ℓ ≥ 1`. -/
theorem lemma_2_4 (q r d : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (hd : 1 ≤ d)
    (T : Matrix (Fin d) (Fin d) ℤ) (S : SmithData q r d T) :
    (matModq q T).rank = r ∧
    Module.finrank (ZMod q) (LinearMap.ker (Matrix.mulVecLin (matModq q T))) = d - r ∧
    |T.det| = (q : ℤ) ^ (d - r) ∧
    (∀ z : Fin d → ℤ, (q : ℤ) • z ∈ imageLattice T) ∧
    Function.Surjective (fun z : Fin d → ℤ => modq q (S.P.mulVec z)) ∧
    (∀ z : Fin d → ℤ, modq q (S.P.mulVec z) = 0 ↔ z ∈ imageLattice T) ∧
    Nat.card ((Fin d → ℤ) ⧸ imageLattice T) = q ^ (d - r) ∧
    (Nontrivial ((Fin d → ℤ) ⧸ imageLattice T) ↔ 1 ≤ d - r) := by sorry

end InfoLossLAR.WorstCase
