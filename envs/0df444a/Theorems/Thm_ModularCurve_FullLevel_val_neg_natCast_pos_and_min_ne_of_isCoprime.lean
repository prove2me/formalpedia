-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_val_neg_natCast_pos_and_min_ne_of_isCoprime
-- name    : ModularCurve.FullLevel.val_neg_natCast_pos_and_min_ne_of_isCoprime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/2fa81018-f402-5815-a971-86d89a170e78
-- title:
--   Two residues modulo qℓ with distinct reduced orders
-- statement:
--   Let $q$ and $\ell$ be natural numbers carrying `Fact` instances that each is prime, and assume $q \ge 5$, $\ell \ge 3$ and $\ell \ne q$; let $g$ be an integer that is coprime to $q$ in $\mathbb{Z}$ (i.e. `IsCoprime g q`, so $g$ and the image of $q$ generate the unit ideal). Work in $\mathbb{Z}/q\ell\mathbb{Z}$ and write $j_1 := (-q).\mathrm{val}$ and $j_2 := (-q - g\ell).\mathrm{val}$ for the canonical representatives in $\{0,\dots,q\ell-1\}$ of the classes of $-q$ and of $-q-g\ell$, where $g$ and $\ell$ are cast into $\mathbb{Z}/q\ell\mathbb{Z}$ from $\mathbb{Z}$ and $\mathbb{N}$ respectively. The conclusion is a sevenfold conjunction: $0 < j_1$, $j_1 < q\ell$, $0 < j_2$, $j_2 < q\ell$, $2 j_1 \neq q\ell$, $2 j_2 \neq q\ell$, and finally $\min(j_1,\, q\ell - j_1) \neq \min(j_2,\, q\ell - j_2)$, all subtraction and comparison being in $\mathbb{N}$.
--
--   This is an elementary admissibility-and-separation statement about two residues modulo $q\ell$: both are non-zero, neither is the half-period, and the two have different distances to $0$ modulo $q\ell$. It is used in the full-level modular curve bookkeeping, namely in [`ModularCurve.FullLevel.AuxLevel.exists_isLevelAutAt_mem_chartAlgFin_coe_eq_slotSubst_sub_and_apply_eq_laurent`](thm.html#ModularCurve.FullLevel.AuxLevel.exists_isLevelAutAt_mem_chartAlgFin_coe_eq_slotSubst_sub_and_apply_eq_laurent), where the two residues index sections whose orders must be distinguished.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_val_neg_natCast_pos_and_min_ne_of_isCoprime.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.FullLevel.val_neg_natCast_pos_and_min_ne_of_isCoprime
    (q ℓ : ℕ) [Fact q.Prime] [Fact ℓ.Prime] (hq : 5 ≤ q) (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (g : ℤ) (hg : IsCoprime g q) :
    0 < (-(q : ZMod (q * ℓ))).val ∧ (-(q : ZMod (q * ℓ))).val < q * ℓ ∧
    0 < (-(q : ZMod (q * ℓ)) - (g : ZMod (q * ℓ)) * (ℓ : ZMod (q * ℓ))).val ∧
    (-(q : ZMod (q * ℓ)) - (g : ZMod (q * ℓ)) * (ℓ : ZMod (q * ℓ))).val < q * ℓ ∧
    2 * (-(q : ZMod (q * ℓ))).val ≠ q * ℓ ∧
    2 * (-(q : ZMod (q * ℓ)) - (g : ZMod (q * ℓ)) * (ℓ : ZMod (q * ℓ))).val ≠ q * ℓ ∧
    min (-(q : ZMod (q * ℓ))).val (q * ℓ - (-(q : ZMod (q * ℓ))).val) ≠
      min (-(q : ZMod (q * ℓ)) - (g : ZMod (q * ℓ)) * (ℓ : ZMod (q * ℓ))).val
        (q * ℓ - (-(q : ZMod (q * ℓ)) - (g : ZMod (q * ℓ)) * (ℓ : ZMod (q * ℓ))).val) := by sorry
