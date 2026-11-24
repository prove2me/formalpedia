-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_cover_detM_a
-- name    : HodgeComputer.SymmetricSexticResidual.Proof.cover_detM_a
-- status  : Proved
-- author  : @benediamond
-- created : 2026-11-24T09:02:00.367685+00:00
-- url     : https://prove2.me/theorems/d06a421a-51af-45aa-a287-0aabb56a5eff
-- title:
--   Mod-1009 evaluation of `c_detM_WP` inputs and $dH/dS$ components
-- statement:
--   Verifies the explicit $\mathbb{F}_{1009}[U]/(P_{34})$ normal forms of the intermediate pairs $A, B, C_c, \xi_S, \xi_Q, a_2, a_0, a_1$ appearing in `Poly1009.c_detM_WP`.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/CoverAlgebra.lean#L1185-L1205

import Definitions.Def_HodgeComputerSSR_CoverParams
set_option autoImplicit false

theorem HodgeComputer.SymmetricSexticResidual.Proof.cover_detM_a :
    let A : SymmetricSexticResidual.CoverAlgebra.Poly1009.Pair1009 := ([0, 0, 0, 693, 99, 24, 990, 960, 985, 475, 392, 1002, 880, 11, 207, 304, 568, 772, 17, 347, 14, 576, 559, 434], [0, 860, 810, 759, 131, 61, 838, 967, 865, 440, 1007, 195, 776, 254, 783, 532, 1007, 241, 289, 723, 854, 784, 543, 526])
    let B : SymmetricSexticResidual.CoverAlgebra.Poly1009.Pair1009 := ([0, 0, 0, 429, 199, 513, 792, 600, 635, 347, 337, 528, 568, 167, 415, 801, 885, 523, 3, 804, 798, 616, 46, 263], [0, 148, 851, 828, 316, 522, 347, 488, 259, 813, 676, 805, 819, 12, 908, 678, 484, 979, 934, 835, 725, 297, 486, 342])
    let Cc : SymmetricSexticResidual.CoverAlgebra.Poly1009.Pair1009 := ([0, 0, 0, 84, 433, 932, 51, 490, 800, 352, 199, 218, 586, 1002, 172, 998, 920, 49, 547, 613, 987, 206, 500, 678], [0, 410, 989, 283, 772, 203, 720, 462, 192, 842, 234, 77, 313, 766, 989, 984, 711, 228, 928, 960, 349, 264, 794, 287])
    let xS : SymmetricSexticResidual.CoverAlgebra.Poly1009.Pair1009 := ([0, 0, 0, 739, 371, 735, 197, 216, 711, 347, 456, 471, 808, 940, 318, 476, 9, 274, 0, 500, 895, 559, 223, 195], [0, 556, 955, 807, 889, 101, 277, 125, 95, 493, 478, 188, 782, 262, 81, 317, 423, 260, 411, 323, 464, 644, 891, 971])
    let xQ : SymmetricSexticResidual.CoverAlgebra.Poly1009.Pair1009 := ([0, 0, 0, 125, 304, 231, 229, 488, 234, 330, 930, 32, 936, 153, 459, 1007, 353, 559, 617, 846, 989, 565, 261, 719], [0, 490, 730, 745, 736, 17, 425, 964, 290, 479, 349, 242, 880, 220, 445, 571, 722, 834, 132, 723, 449, 316, 961, 160])
    let ax : SymmetricSexticResidual.CoverAlgebra.Poly1009.Pair1009 := ([0, 0, 0, 423, 470, 759, 178, 167, 687, 822, 848, 464, 679, 951, 525, 780, 577, 37, 17, 847, 909, 126, 782, 629], [0, 407, 756, 557, 11, 162, 106, 83, 960, 933, 476, 383, 549, 516, 864, 849, 421, 501, 700, 37, 309, 419, 425, 488])
    let bx : SymmetricSexticResidual.CoverAlgebra.Poly1009.Pair1009 := ([0, 0, 0, 554, 503, 744, 12, 79, 869, 677, 258, 560, 495, 320, 874, 799, 229, 73, 620, 641, 778, 172, 307, 982], [0, 638, 572, 564, 43, 539, 772, 443, 549, 283, 16, 38, 690, 232, 344, 240, 197, 804, 57, 549, 165, 613, 438, 502])
    let a2 : SymmetricSexticResidual.CoverAlgebra.Poly1009.Pair1009 := ([950, 858, 321, 742, 159, 570, 523, 24, 870, 55, 220, 198, 814, 879, 28, 223, 354, 739, 761, 826, 80, 299, 685, 853, 939, 749, 319, 227, 892, 486, 971, 844, 118, 239], [32, 980, 181, 59, 72, 17, 179, 888, 369, 855, 328, 929, 782, 134, 486, 6, 897, 780, 382, 136, 391, 183, 430, 160, 964, 190, 28, 404, 802, 591, 93, 492, 199, 45])
    let a0 : SymmetricSexticResidual.CoverAlgebra.Poly1009.Pair1009 := ([364, 80, 930, 853, 79, 156, 738, 602, 816, 649, 124, 186, 364, 226, 355, 293, 743, 801, 938, 692, 286, 796, 985, 55, 290, 333, 894, 639, 285, 144, 562, 228, 169, 701], [304, 527, 903, 155, 9, 98, 865, 718, 656, 770, 114, 485, 848, 353, 136, 146, 457, 373, 149, 949, 757, 787, 14, 730, 379, 191, 523, 303, 202, 61, 53, 38, 482, 1007])
    let a1_0 : SymmetricSexticResidual.CoverAlgebra.Poly1009.Pair1009 := ([949, 947, 539, 596, 71, 117, 728, 976, 329, 741, 5, 415, 497, 198, 113, 355, 787, 517, 749, 882, 658, 215, 34, 751, 996, 402, 7, 280, 370, 971, 55, 192, 236, 594], [595, 899, 551, 606, 408, 719, 437, 762, 823, 926, 16, 205, 561, 845, 760, 741, 966, 563, 176, 283, 143, 430, 290, 169, 886, 382, 673, 795, 731, 909, 322, 884, 232, 47])
    let a1 : SymmetricSexticResidual.CoverAlgebra.Poly1009.Pair1009 := ([644, 9, 297, 10, 842, 400, 476, 350, 661, 37, 670, 31, 328, 102, 739, 848, 699, 995, 59, 373, 292, 129, 382, 852, 776, 329, 812, 423, 202, 341, 540, 129, 958, 663], [259, 401, 476, 392, 327, 604, 402, 165, 807, 310, 583, 809, 949, 358, 138, 589, 621, 419, 654, 207, 4, 469, 855, 288, 552, 1, 122, 88, 736, 257, 176, 354, 560, 4])
    (SymmetricSexticResidual.CoverAlgebra.Poly1009.qmodP (SymmetricSexticResidual.CoverAlgebra.Poly1009.qsc (SymmetricSexticResidual.CoverAlgebra.Poly1009.pneg SymmetricSexticResidual.CoverAlgebra.Poly1009.c_cb_h) SymmetricSexticResidual.CoverAlgebra.Poly1009.c_d0_z) = A) ∧
    (SymmetricSexticResidual.CoverAlgebra.Poly1009.qmodP (SymmetricSexticResidual.CoverAlgebra.Poly1009.qsub (SymmetricSexticResidual.CoverAlgebra.Poly1009.qsc SymmetricSexticResidual.CoverAlgebra.Poly1009.c_ca_h SymmetricSexticResidual.CoverAlgebra.Poly1009.c_d0_z) (SymmetricSexticResidual.CoverAlgebra.Poly1009.qmul SymmetricSexticResidual.CoverAlgebra.Poly1009.c_c0W SymmetricSexticResidual.CoverAlgebra.Poly1009.c_d1_z)) = B) ∧
    (SymmetricSexticResidual.CoverAlgebra.Poly1009.qmodP (SymmetricSexticResidual.CoverAlgebra.Poly1009.qmul SymmetricSexticResidual.CoverAlgebra.Poly1009.c_W (SymmetricSexticResidual.CoverAlgebra.Poly1009.qsc SymmetricSexticResidual.CoverAlgebra.Poly1009.c_cb_h SymmetricSexticResidual.CoverAlgebra.Poly1009.c_d1_z)) = Cc) ∧
    (SymmetricSexticResidual.CoverAlgebra.Poly1009.qsubP (SymmetricSexticResidual.CoverAlgebra.Poly1009.qscP [SymmetricSexticResidual.CoverAlgebra.Poly1009.params1009.S] Cc) (SymmetricSexticResidual.CoverAlgebra.Poly1009.qscP [SymmetricSexticResidual.CoverAlgebra.Poly1009.params1009.T] A) = xS) ∧
    (SymmetricSexticResidual.CoverAlgebra.Poly1009.qsubP (SymmetricSexticResidual.CoverAlgebra.Poly1009.qscP [SymmetricSexticResidual.CoverAlgebra.Poly1009.params1009.Q] Cc) (SymmetricSexticResidual.CoverAlgebra.Poly1009.qscP [SymmetricSexticResidual.CoverAlgebra.Poly1009.params1009.T] B) = xQ) ∧
    (SymmetricSexticResidual.CoverAlgebra.Poly1009.qaddP A xS = ax) ∧
    (SymmetricSexticResidual.CoverAlgebra.Poly1009.qaddP B xQ = bx) ∧
    (SymmetricSexticResidual.CoverAlgebra.Poly1009.c_dH_dS_homP A B = a2) ∧
    (SymmetricSexticResidual.CoverAlgebra.Poly1009.c_dH_dS_homP xS xQ = a0) ∧
    (SymmetricSexticResidual.CoverAlgebra.Poly1009.c_dH_dS_homP ax bx = a1_0) ∧
    (SymmetricSexticResidual.CoverAlgebra.Poly1009.qsubP (SymmetricSexticResidual.CoverAlgebra.Poly1009.qsubP a1_0 a2) a0 = a1) := by sorry
